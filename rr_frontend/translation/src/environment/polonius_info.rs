// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::collections::HashMap;

use log::{debug, trace};
use rr_rustc_interface::middle::ty::TypeFolder as _;
use rr_rustc_interface::middle::{mir, ty};
use rr_rustc_interface::{data_structures, polonius_engine};

use crate::environment::Environment;
use crate::environment::borrowck::facts;
use crate::environment::procedure::Procedure;
use crate::environment::region_folder::*;

/// This represents "rich" regions that are directly annotated with their `RegionKind`.
///
/// `PlaceRegions` are a bit special: in Polonius, they contain sets of loans, but in RR's
/// path-sensitive type system they also end up referencing one particular loan.
///
/// Loan regions can themselves be intersections of other loan regions and universal regions,
/// but they contain an "atomic" component (corresponding to an atomic lifetime).
#[derive(Copy, Clone, Debug)]
pub(crate) enum AtomicRegion {
    Loan(facts::Region),
    Universal(UniversalRegionKind, facts::Region),
    PlaceRegion(facts::Region, bool),
    Unknown(facts::Region, bool),
}

impl AtomicRegion {
    #[must_use]
    pub(crate) const fn is_place(self) -> bool {
        matches!(self, Self::PlaceRegion(_, _))
    }

    #[must_use]
    pub(crate) const fn is_value(self) -> bool {
        matches!(self, Self::Unknown(_, _))
    }

    #[must_use]
    pub(crate) const fn is_loan(self) -> bool {
        matches!(self, Self::Loan(_))
    }

    #[must_use]
    pub(crate) const fn is_unconstrained(self) -> bool {
        match self {
            Self::PlaceRegion(_, b) | Self::Unknown(_, b) => b,
            _ => false,
        }
    }

    #[must_use]
    pub(crate) const fn get_region(self) -> facts::Region {
        match self {
            Self::Loan(r) | Self::Universal(_, r) | Self::PlaceRegion(r, _) | Self::Unknown(r, _) => r,
        }
    }
}

/// for an overview fo universal regions, see also `borrowck/src/universal_regions.rs`
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub(crate) enum UniversalRegionKind {
    /// the static region
    Static,
    /// the function-level region
    Function,
    /// a locally declared universal region (except for the function region)
    Local,
}

#[derive(Debug)]
pub(crate) enum RegionKind {
    /// this region belongs to a loan that is created
    Loan,
    /// this is a universal region
    Universal(UniversalRegionKind),
    /// inference variable in the type of a local
    /// boolean indicates whether it is unconstrained
    PlaceRegion(bool),
    /// unknown region kind; for instance used for the inference variables introduced on a call to
    /// a function with lifetime parameters
    /// boolean indicates whether it is unconstrained
    Unknown(bool),
}

/// Compute the transitive closure of a vec of constraints between regions.
#[must_use]
pub(crate) fn compute_transitive_closure(
    constraints: Vec<(facts::Region, facts::Region)>,
) -> Vec<(facts::Region, facts::Region)> {
    let mut iter = datafrog::Iteration::new();

    let incl = iter.variable::<(facts::Region, facts::Region)>("incl");
    incl.extend(constraints);

    let incl1 = iter.variable_indistinct::<(facts::Region, facts::Region)>("incl1");

    while iter.changed() {
        incl1.from_map(&incl, |(r1, r2)| (*r2, *r1));
        incl.from_join(&incl1, &incl, |_r2, r1, r3| (*r1, *r3));
    }
    let incl = incl.complete();
    incl.elements
}

// Terminology: zombie loans are loans that are loan_killed_at.
pub(crate) struct PoloniusInfo<'a, 'tcx> {
    pub(crate) tcx: ty::TyCtxt<'tcx>,
    pub(crate) mir: &'a mir::Body<'tcx>,
    pub(crate) borrowck_in_facts: &'tcx facts::AllInput,
    pub(crate) borrowck_out_facts: facts::AllOutput,
    pub(crate) interner: facts::Interner<'tcx>,
    /// Position at which a specific loan was created.
    pub(crate) loan_position: HashMap<facts::Loan, mir::Location>,
    pub(crate) loan_at_position: HashMap<mir::Location, facts::Loan>,
    pub(crate) additional_facts: AdditionalFacts,
}

impl<'a, 'tcx: 'a> PoloniusInfo<'a, 'tcx> {
    pub(crate) fn new(env: &'a Environment<'tcx>, procedure: &'a Procedure<'tcx>) -> Self {
        let tcx = procedure.get_tcx();
        let def_id = procedure.get_id();
        let mir = procedure.get_mir();

        // Read Polonius facts.
        let facts = env.local_mir_borrowck_facts(def_id.expect_local());

        let interner = facts::Interner::new(facts.location_table.as_ref().unwrap());
        let all_facts = facts.input_facts.as_ref().unwrap();

        let output = polonius_engine::Output::compute(all_facts, polonius_engine::Algorithm::Naive, true);

        let loan_position: HashMap<_, _> = all_facts
            .loan_issued_at
            .iter()
            .map(|&(_, loan, point_index)| {
                let point = interner.get_point(point_index);
                (loan, point.location)
            })
            .collect();
        let loan_at_position: HashMap<_, _> = all_facts
            .loan_issued_at
            .iter()
            .map(|&(_, loan, point_index)| {
                let point = interner.get_point(point_index);
                (point.location, loan)
            })
            .collect();

        let additional_facts = AdditionalFacts::new(all_facts, &output);

        Self {
            tcx,
            mir,
            borrowck_in_facts: all_facts,
            borrowck_out_facts: output,
            interner,
            loan_position,
            loan_at_position,
            additional_facts,
        }
    }

    /// Gets the kind of a region: originating from a loan, a universal region, or none of these.
    #[must_use]
    pub(crate) fn get_region_kind(&self, region: facts::Region) -> RegionKind {
        // check if this region is induced by a loan
        let v: Vec<facts::Loan> = self
            .borrowck_in_facts
            .loan_issued_at
            .iter()
            .filter_map(|(r, loan, _)| (r == &region).then_some(*loan))
            .collect();

        if !v.is_empty() {
            if v.len() == 1 {
                return RegionKind::Loan;
            }

            unreachable!("A region should not be induced by multiple loans");
        }

        // check if this is a universal region
        if self.borrowck_in_facts.placeholder.iter().any(|(r, _)| r == &region) {
            // this is a universal region
            if region.index() == 0 {
                return RegionKind::Universal(UniversalRegionKind::Static);
            }

            if region.index() + 1 == self.borrowck_in_facts.placeholder.len() {
                // TODO check if this does the right thing
                return RegionKind::Universal(UniversalRegionKind::Function);
            }

            // TODO: this ignores external regions
            return RegionKind::Universal(UniversalRegionKind::Local);
        }

        // check if this is an unconstrained region
        let unconstrained = !self.borrowck_in_facts.subset_base.iter().any(|(_, r2, _)| *r2 == region);

        // check if this is a place region
        let mut found_region = false;
        let mut clos = |r: ty::Region<'tcx>, _| match r.kind() {
            ty::RegionKind::ReVar(rv) if rv == region.into() => {
                found_region = true;
                r
            },
            _ => r,
        };

        let mut folder = RegionFolder::new(self.tcx, &mut clos);
        for local in &self.mir.local_decls {
            folder.fold_ty(local.ty);
        }

        if found_region {
            return RegionKind::PlaceRegion(unconstrained);
        }

        RegionKind::Unknown(unconstrained)
    }

    #[must_use]
    pub(crate) fn mk_atomic_region(&self, r: facts::Region) -> AtomicRegion {
        let kind = self.get_region_kind(r);
        match kind {
            RegionKind::Loan => AtomicRegion::Loan(r),
            RegionKind::PlaceRegion(b) => AtomicRegion::PlaceRegion(r, b),
            RegionKind::Universal(uk) => AtomicRegion::Universal(uk, r),
            RegionKind::Unknown(b) => AtomicRegion::Unknown(r, b),
        }
    }

    /// Get new subset constraints generated at a point.
    #[must_use]
    pub(crate) fn get_new_subset_constraints_at_point(
        &self,
        point: facts::PointIndex,
    ) -> Vec<(facts::Region, facts::Region)> {
        let root_location = mir::Location {
            block: mir::BasicBlock::from_u32(0),
            statement_index: 0,
        };
        let root_point = self.interner.get_point_index(&facts::Point {
            location: root_location,
            typ: facts::PointType::Mid,
        });

        let mut constraints = Vec::new();
        for (r1, r2, p) in &self.borrowck_in_facts.subset_base {
            // only if the root doesn't also contain the constraint
            if *p == point && !self.borrowck_in_facts.subset_base.contains(&(*r1, *r2, root_point)) {
                constraints.push((*r1, *r2));
            }
        }
        constraints
    }

    #[must_use]
    pub(crate) fn get_point(
        &self,
        location: mir::Location,
        point_type: facts::PointType,
    ) -> facts::PointIndex {
        let point = facts::Point {
            location,
            typ: point_type,
        };
        self.interner.get_point_index(&point)
    }

    /// Get loans that die at the given location.
    pub(crate) fn get_dying_loans(&self, location: mir::Location) -> Vec<facts::Loan> {
        self.get_loans_dying_at(location, false)
    }

    /// Get loans that die at the given location.
    pub(crate) fn get_dying_zombie_loans(&self, location: mir::Location) -> Vec<facts::Loan> {
        self.get_loans_dying_at(location, true)
    }

    /// Get the atomic region corresponding to a loan.
    #[must_use]
    pub(crate) fn atomic_region_of_loan(&self, l: facts::Loan) -> AtomicRegion {
        let r = self.get_loan_issued_at_for_loan(l);
        AtomicRegion::Loan(r)
    }

    fn get_borrow_live_at(
        &self,
        zombie: bool,
    ) -> data_structures::fx::FxHashMap<facts::PointIndex, Vec<facts::Loan>> {
        if zombie {
            self.additional_facts.zombie_borrow_live_at.clone()
        } else {
            self.borrowck_out_facts
                .loan_live_at
                .iter()
                .map(|(a, b)| (a.to_owned(), b.to_owned()))
                .collect()
        }
    }

    /// Get loans that are active (including those that are about to die) at the given location.
    #[must_use]
    pub(crate) fn get_active_loans(&self, location: mir::Location, zombie: bool) -> Vec<facts::Loan> {
        let loan_live_at = self.get_borrow_live_at(zombie);
        let start_point = self.get_point(location, facts::PointType::Start);
        let mid_point = self.get_point(location, facts::PointType::Mid);

        let mut loans = if let Some(mid_loans) = loan_live_at.get(&mid_point) {
            let mut mid_loans = mid_loans.clone();
            mid_loans.sort();
            let default_vec = vec![];
            let start_loans = loan_live_at.get(&start_point).unwrap_or(&default_vec);
            let mut start_loans = start_loans.clone();
            start_loans.sort();
            debug!("start_loans = {:?}", start_loans);
            debug!("mid_loans = {:?}", mid_loans);
            // Loans are created in mid point, so mid_point may contain more loans than the start
            // point.
            assert!(start_loans.iter().all(|loan| mid_loans.contains(loan)));

            mid_loans
        } else {
            assert!(!loan_live_at.contains_key(&start_point));
            vec![]
        };
        if !zombie {
            for (_, loan, point) in &self.borrowck_in_facts.loan_issued_at {
                if point == &mid_point && !loans.contains(loan) {
                    loans.push(*loan);
                }
            }
        }
        loans
    }

    /// Get loans that die *at* (that is, exactly after) the given location.
    #[must_use]
    pub(crate) fn get_loans_dying_at(&self, location: mir::Location, zombie: bool) -> Vec<facts::Loan> {
        // TODO: this needs to change.
        // the problem is that we check explcitly that it is currently live, but not at the next
        // point.
        // there are loans dying where there might be no such point in case of branching flow.
        // what's a better rule?
        // maybe: check for loans which are not live now, but in one of the potential predecessors
        // maybe use loans_dying_between?
        // - I can't determine this in a forward-analysis way at a goto.
        // - instead: check predecessors in CFG.

        // loans live at point
        let loan_live_at = self.get_borrow_live_at(zombie);
        let successors = self.get_successors(location);
        let is_return = is_return(self.mir, location);
        let mid_point = self.get_point(location, facts::PointType::Mid);
        // get loans killed at point
        let becoming_zombie_loans =
            self.additional_facts.borrow_become_zombie_at.get(&mid_point).cloned().unwrap_or_default();
        self.get_active_loans(location, zombie)
            .into_iter()
            // active loans which are neither alive in the successor nor returned
            .filter(|loan| {
                // check if it is alive in successor
                let alive_in_successor = successors.iter().any(|successor_location| {
                    let point = self.get_point(*successor_location, facts::PointType::Start);
                    loan_live_at.get(&point).is_some_and(|successor_loans| successor_loans.contains(loan))
                });
                // alive in successor or returned
                !(alive_in_successor || (successors.is_empty() && is_return))
            })
            // filter out zombies (that are killed but where the loan is still ongoing)
            .filter(|loan| !becoming_zombie_loans.contains(loan))
            .collect()
    }

    /// Get loans that die between two consecutive locations.
    #[must_use]
    pub(crate) fn get_loans_dying_between(
        &self,
        initial_loc: mir::Location,
        final_loc: mir::Location,
        zombie: bool,
    ) -> Vec<facts::Loan> {
        trace!("[enter] get_loans_dying_between {:?}, {:?}, {}", initial_loc, final_loc, zombie);
        debug_assert!(self.get_successors(initial_loc).contains(&final_loc));
        let mid_point = self.get_point(initial_loc, facts::PointType::Mid);
        let becoming_zombie_loans =
            self.additional_facts.borrow_become_zombie_at.get(&mid_point).cloned().unwrap_or_default();
        trace!("becoming_zombie_loans={:?}", becoming_zombie_loans);
        let final_loc_point = self.get_point(final_loc, facts::PointType::Start);
        trace!("loan_live_at final {:?}", self.borrowck_out_facts.loan_live_at.get(&final_loc_point));
        let dying_loans = self
            .get_active_loans(initial_loc, zombie)
            .into_iter()
            .filter(|loan| {
                self.get_borrow_live_at(zombie)
                    .get(&final_loc_point)
                    .is_none_or(|successor_loans| !successor_loans.contains(loan))
            })
            .filter(|loan| !becoming_zombie_loans.contains(loan))
            .collect();
        trace!(
            "[exit] get_loans_dying_between {:?}, {:?}, {}, dying_loans={:?}",
            initial_loc, final_loc, zombie, dying_loans
        );
        dying_loans
    }

    /// Get the location at which a loan is created, if possible
    #[must_use]
    pub(crate) fn get_loan_location(&self, loan: facts::Loan) -> Option<mir::Location> {
        self.loan_position.get(&loan).copied()
    }

    /// Get the loan that gets created at a location.
    /// TODO: for aggregates, this only finds one loan
    #[must_use]
    pub(crate) fn get_optional_loan_at_location(&self, location: mir::Location) -> Option<facts::Loan> {
        self.loan_at_position.contains_key(&location).then(|| self.loan_at_position[&location])
    }

    /// Returns the borrow region that requires the terms of the given loan to be enforced. This
    /// does *not* return all regions that require the terms of the loan to be enforced. So for the
    /// following MIR code, it returns the region '2rv but not the region '1rv:
    ///
    /// ```ignore
    /// let _1: &'1rv u32;
    /// _1 = &'2rv 123;
    /// ```
    fn get_loan_issued_at_for_loan(&self, loan: facts::Loan) -> facts::Region {
        let location = self.get_loan_location(loan).unwrap();
        let point = self.get_point(location, facts::PointType::Mid);
        let regions = self
            .borrowck_in_facts
            .loan_issued_at
            .iter()
            .filter_map(|&(r, l, p)| (p == point && l == loan).then_some(r))
            .collect::<Vec<_>>();

        if regions.len() == 1 {
            regions[0]
        } else {
            unreachable!(
                "Cannot determine region for loan {:?}, because there is not exactly one possible option: {:?}",
                loan, regions
            )
        }
    }

    fn get_successors(&self, location: mir::Location) -> Vec<mir::Location> {
        let statements_len = self.mir[location.block].statements.len();
        if location.statement_index < statements_len {
            vec![mir::Location {
                statement_index: location.statement_index + 1,
                ..location
            }]
        } else {
            let mut successors = Vec::new();
            for successor in self.mir[location.block].terminator.as_ref().unwrap().successors() {
                successors.push(mir::Location {
                    block: successor,
                    statement_index: 0,
                });
            }
            successors
        }
    }
}

/// Check if the terminator is return.
fn is_return(mir: &mir::Body<'_>, location: mir::Location) -> bool {
    let mir::BasicBlockData {
        statements,
        terminator,
        ..
    } = &mir[location.block];

    if statements.len() != location.statement_index {
        return false;
    }

    matches!(terminator.as_ref().unwrap().kind, mir::TerminatorKind::Return)
}

/// Additional facts derived from the borrow checker facts.
pub(crate) struct AdditionalFacts {
    /// The ``zombie_borrow_live_at`` facts are ``loan_live_at`` facts
    /// for the loans that were `loan_killed_at`.
    ///
    /// ```datalog
    /// zombie_borrow_live_at(L, P) :-
    ///     zombie_requires(R, L, P),
    ///     origin_live_on_entry(R, P).
    /// ```
    pub(crate) zombie_borrow_live_at: data_structures::fx::FxHashMap<facts::PointIndex, Vec<facts::Loan>>,

    /// Which loans were `loan_killed_at` (become zombies) at a given point.
    pub(crate) borrow_become_zombie_at: data_structures::fx::FxHashMap<facts::PointIndex, Vec<facts::Loan>>,
}

impl AdditionalFacts {
    /// Derive ``zombie_requires``.
    fn derive_zombie_requires(
        all_facts: &facts::AllInput,
        output: &facts::AllOutput,
    ) -> (
        data_structures::fx::FxHashMap<facts::PointIndex, Vec<facts::Loan>>,
        data_structures::fx::FxHashMap<facts::PointIndex, Vec<facts::Loan>>,
    ) {
        use datafrog::{Iteration, Relation};
        use facts::{Loan, PointIndex, Region};

        let mut iteration = Iteration::new();

        // Variables that are outputs of our computation.
        let zombie_requires = iteration.variable::<(Region, Loan, PointIndex)>("zombie_requires");
        let zombie_borrow_live_at = iteration.variable::<(Loan, PointIndex)>("zombie_borrow_live_at");
        let borrow_become_zombie_at = iteration.variable::<(Loan, PointIndex)>("borrow_become_zombie_at");

        // Variables for initial data.
        let requires_lp = iteration.variable::<((Loan, PointIndex), Region)>("requires_lp");
        let loan_killed_at = iteration.variable::<((Loan, PointIndex), ())>("loan_killed_at");
        let cfg_edge_p = iteration.variable::<(PointIndex, PointIndex)>("cfg_edge_p");
        let origin_live_on_entry = iteration.variable::<((Region, PointIndex), ())>("origin_live_on_entry");
        let subset_r1p = iteration.variable::<((Region, PointIndex), Region)>("subset_r1p");

        // Temporaries as we perform a multi-way join.
        let zombie_requires_rp = iteration.variable_indistinct("zombie_requires_rp");
        let zombie_requires_p = iteration.variable_indistinct("zombie_requires_p");
        let zombie_requires_1 = iteration.variable_indistinct("zombie_requires_1");
        let zombie_requires_2 = iteration.variable_indistinct("zombie_requires_2");
        let zombie_requires_3 = iteration.variable_indistinct("zombie_requires_3");
        let zombie_requires_4 = iteration.variable_indistinct("zombie_requires_4");

        // Load initial facts.
        requires_lp.insert(Relation::from_iter(output.origin_contains_loan_at.iter().flat_map(
            |(&point, region_map)| {
                region_map
                    .iter()
                    .flat_map(move |(&region, loans)| loans.iter().map(move |&loan| ((loan, point), region)))
            },
        )));
        loan_killed_at.insert(Relation::from_iter(
            all_facts.loan_killed_at.iter().map(|&(loan, point)| ((loan, point), ())),
        ));
        cfg_edge_p.insert(all_facts.cfg_edge.clone().into());

        let origin_live_on_entry_vec = {
            output.origin_live_on_entry.iter().flat_map(|(point, origins)| {
                origins.iter().copied().map(|origin| (origin, *point)).collect::<Vec<_>>()
            })
        };
        origin_live_on_entry.insert(Relation::from_iter(origin_live_on_entry_vec.map(|(r, p)| ((r, p), ()))));
        subset_r1p.insert(Relation::from_iter(output.subset.iter().flat_map(|(&point, subset_map)| {
            subset_map.iter().flat_map(move |(&region1, regions)| {
                regions.iter().map(move |&region2| ((region1, point), region2))
            })
        })));

        while iteration.changed() {
            zombie_requires_rp.from_map(&zombie_requires, |&(r, l, p)| ((r, p), l));
            zombie_requires_p.from_map(&zombie_requires, |&(r, l, p)| (p, (l, r)));

            // zombie_requires(R, L, Q) :-
            //     requires(R, L, P),
            //     loan_killed_at(L, P),
            //     cfg_edge(P, Q),
            //     origin_live_on_entry(R, Q).
            zombie_requires_1.from_join(&requires_lp, &loan_killed_at, |&(l, p), &r, ()| (p, (l, r)));
            zombie_requires_2.from_join(&zombie_requires_1, &cfg_edge_p, |&_p, &(l, r), &q| ((r, q), l));
            zombie_requires
                .from_join(&zombie_requires_2, &origin_live_on_entry, |&(r, q), &l, &()| (r, l, q));
            zombie_requires_4.from_join(&zombie_requires_1, &cfg_edge_p, |&p, &(l, r), &q| ((r, q), (p, l)));
            borrow_become_zombie_at.from_join(
                &zombie_requires_4,
                &origin_live_on_entry,
                |_, &(p, l), &()| (l, p),
            );

            // zombie_requires(R2, L, P) :-
            //     zombie_requires(R1, L, P),
            //     subset(R1, R2, P).
            zombie_requires.from_join(&zombie_requires_rp, &subset_r1p, |&(_r1, p), &b, &r2| (r2, b, p));

            // zombie_requires(R, L, Q) :-
            //     zombie_requires(R, L, P),
            //     cfg_edge(P, Q),
            //     origin_live_on_entry(R, Q).
            zombie_requires_3.from_join(&zombie_requires_p, &cfg_edge_p, |&_p, &(l, r), &q| ((r, q), l));
            zombie_requires
                .from_join(&zombie_requires_3, &origin_live_on_entry, |&(r, q), &l, &()| (r, l, q));

            // zombie_borrow_live_at(L, P) :-
            //     zombie_requires(R, L, P),
            //     origin_live_on_entry(R, P).
            zombie_borrow_live_at.from_join(
                &zombie_requires_rp,
                &origin_live_on_entry,
                |&(_r, p), &l, &()| (l, p),
            );
        }

        let zombie_borrow_live_at = zombie_borrow_live_at.complete();
        let mut zombie_borrow_live_at_map = data_structures::fx::FxHashMap::default();
        for (loan, point) in &zombie_borrow_live_at.elements {
            zombie_borrow_live_at_map.entry(*point).or_insert_with(Vec::new).push(*loan);
        }

        let borrow_become_zombie_at = borrow_become_zombie_at.complete();
        let mut borrow_become_zombie_at_map = data_structures::fx::FxHashMap::default();
        for (loan, point) in &borrow_become_zombie_at.elements {
            borrow_become_zombie_at_map.entry(*point).or_insert_with(Vec::new).push(*loan);
        }

        (zombie_borrow_live_at_map, borrow_become_zombie_at_map)
    }

    /// Derive additional facts from the borrow checker facts.
    #[must_use]
    pub(crate) fn new(all_facts: &facts::AllInput, output: &facts::AllOutput) -> Self {
        let (zombie_borrow_live_at, borrow_become_zombie_at) =
            Self::derive_zombie_requires(all_facts, output);

        Self {
            zombie_borrow_live_at,
            borrow_become_zombie_at,
        }
    }
}
