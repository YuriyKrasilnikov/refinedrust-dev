// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::fmt;

use rr_rustc_interface::borrowck;
use rr_rustc_interface::borrowck::consumers::{PoloniusLocationTable, RichLocation, RustcFacts};
use rr_rustc_interface::middle::mir;
use rr_rustc_interface::polonius_engine::FactTypes;

pub(crate) type Region = <RustcFacts as FactTypes>::Origin;
pub(crate) type Loan = <RustcFacts as FactTypes>::Loan;
pub(crate) type PointIndex = <RustcFacts as FactTypes>::Point;

pub(crate) type AllInput = borrowck::consumers::PoloniusInput;
pub(crate) type AllOutput = borrowck::consumers::PoloniusOutput;

pub(crate) struct Borrowck<'tcx> {
    /// Polonius input facts.
    pub input_facts: &'tcx Option<Box<AllInput>>,
    /// The table that maps Polonius points to locations in the table.
    pub location_table: &'tcx Option<PoloniusLocationTable>,
}

/// The type of the point. Either the start of a statement or in the
/// middle of it.
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub(crate) enum PointType {
    Start,
    Mid,
}

/// A program point used in the borrow checker analysis.
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub(crate) struct Point {
    pub location: mir::Location,
    pub typ: PointType,
}

impl fmt::Display for Point {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}:{:?}:{:?}", self.location.block, self.location.statement_index, self.typ)
    }
}

pub(crate) struct Interner<'tcx> {
    pub(crate) location_table: &'tcx PoloniusLocationTable,
}

impl<'tcx> Interner<'tcx> {
    #[must_use]
    pub(crate) const fn new(location_table: &'tcx PoloniusLocationTable) -> Self {
        Self { location_table }
    }

    #[must_use]
    pub(crate) fn get_point_index(&self, point: &Point) -> PointIndex {
        match point.typ {
            PointType::Start => self.location_table.start_index(point.location),
            PointType::Mid => self.location_table.mid_index(point.location),
        }
    }

    #[must_use]
    pub(crate) fn get_point(&self, index: PointIndex) -> Point {
        match self.location_table.to_rich_location(index) {
            RichLocation::Start(location) => Point {
                location,
                typ: PointType::Start,
            },
            RichLocation::Mid(location) => Point {
                location,
                typ: PointType::Mid,
            },
        }
    }
}
