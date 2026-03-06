// © 2019, ETH Zurich
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::collections::BTreeMap;
use std::fs::File;
use std::io::{BufWriter, Write as _};
use std::marker::PhantomData;
use std::{fs, io};

use log::{debug, trace};
use rr_rustc_interface::hir::def_id::DefId;
use rr_rustc_interface::middle::ty;

use crate::environment::polonius_info::PoloniusInfo;

pub(crate) fn dump_borrowck_info<'a, 'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    procedure: DefId,
    info: &'a PoloniusInfo<'a, 'tcx>,
) {
    trace!("[dump_borrowck_info] enter");

    let printer = InfoPrinter {
        tcx,
        phantom: PhantomData,
    };

    printer.print_info(procedure, info);

    trace!("[dump_borrowck_info] exit");
}

struct InfoPrinter<'a, 'tcx: 'a> {
    tcx: ty::TyCtxt<'tcx>,
    phantom: PhantomData<&'a ()>,
}

impl<'a, 'tcx: 'a> InfoPrinter<'a, 'tcx> {
    fn dump_borrowck_facts(info: &'a PoloniusInfo<'a, 'tcx>, writer: &mut BufWriter<File>) -> io::Result<()> {
        let input_facts = &info.borrowck_in_facts;
        let interner = &info.interner;
        write!(writer, "======== Borrowck facts ========\n\n")?;

        write!(writer, "Loans issued at: \n")?;
        for issued in &input_facts.loan_issued_at {
            let loc = interner.get_point(issued.2);
            write!(writer, "({:?}, {:?}, {:?})\n", issued.0, issued.1, loc)?;
        }
        write!(writer, "\n\n")?;

        write!(writer, "Use of var derefs origin: \n")?;
        write!(writer, "{:?}", input_facts.use_of_var_derefs_origin)?;
        write!(writer, "\n\n")?;

        write!(writer, "Loans killed at: \n")?;
        for fact in &input_facts.loan_killed_at {
            let loc = interner.get_point(fact.1);
            write!(writer, "({:?}, {:?})\n", fact.0, loc)?;
        }
        write!(writer, "\n\n")?;

        write!(writer, "Loans invalidated at: \n")?;
        for fact in &input_facts.loan_invalidated_at {
            let loc = interner.get_point(fact.0);
            write!(writer, "({:?}, {:?})\n", loc, fact.1)?;
        }
        write!(writer, "\n\n")?;

        write!(writer, "Known placeholders:\n")?;
        for fact in &input_facts.placeholder {
            write!(writer, "({:?}, {:?})\n", fact.0, fact.1)?;
        }
        write!(writer, "\n\n")?;

        write!(writer, "known placeholder subset: \n")?;
        for fact in &input_facts.known_placeholder_subset {
            write!(writer, "({:?}, {:?})\n", fact.0, fact.1)?;
        }
        write!(writer, "\n\n")?;

        write!(writer, "Subset (base, take transitive closure): \n")?;
        for fact in &input_facts.subset_base {
            write!(writer, "({:?} ⊑ {:?}, {:?})\n", fact.0, fact.1, interner.get_point(fact.2))?;
        }
        write!(writer, "\n\n")?;

        let output_facts = &info.borrowck_out_facts;

        write!(writer, "Subset:\n")?;
        let v: BTreeMap<_, _> = info.borrowck_out_facts.subset.iter().collect();
        for (l, m) in v {
            write!(writer, "({:?}, {:?})\n", interner.get_point(*l).location, m)?;
        }
        write!(writer, "\n\n")?;

        write!(writer, "Origin contains loan at: \n")?;
        let mut sorted_origin_contains: Vec<_> = output_facts.origin_contains_loan_at.iter().collect();
        sorted_origin_contains.sort_by_key(|&(&l1, _)| l1);

        for &(&loc, region_map) in &sorted_origin_contains {
            write!(writer, "\t {:?} -> {:?}\n", interner.get_point(loc), region_map)?;
        }
        write!(writer, "\n\n")?;

        write!(writer, "Dump enabled: {:?}\n", output_facts.dump_enabled)?;

        Ok(())
    }

    fn print_info(&self, def_id: DefId, info: &'a PoloniusInfo<'a, 'tcx>) {
        trace!("[print_info] enter {:?}", def_id);

        let local_def_id = def_id.expect_local();

        // Read Polonius facts.
        let def_path = self.tcx.hir_def_path(local_def_id);

        // write raw dump
        let raw_path = rrconfig::log_dir()
            .unwrap()
            .join("nll-facts")
            .join(def_path.to_filename_friendly_no_crate())
            .join("polonius_info.txt");
        debug!("Writing raw polonius info to {}", raw_path.display());

        let prefix = raw_path.parent().expect("Unable to determine parent dir");
        fs::create_dir_all(prefix).expect("Unable to create parent dir");
        let raw_file = File::create(raw_path).expect("Unable to create file");
        let mut raw = BufWriter::new(raw_file);
        Self::dump_borrowck_facts(info, &mut raw).unwrap();

        trace!("[print_info] exit");
    }
}
