// This file uses code from the Prusti project under the MPL 2.0 license.
//
// Other parts of the source are © 2023, The RefinedRust Developers and Contributors
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

#![feature(rustc_private)]
#![feature(exitcode_exit_method)]

use std::path::PathBuf;
use std::process::Command;
use std::{env, process};

use log::{debug, info};
use rr_rustc_interface::hir::def_id::LocalDefId;
use rr_rustc_interface::middle::{queries, query, ty, util};
use rr_rustc_interface::{borrowck, driver, interface, session};

const BUG_REPORT_URL: &str = "https://gitlab.mpi-sws.org/lgaeher/refinedrust-dev/-/issues/new";

/// Callbacks for the `RefinedRust` frontend.
struct RRCompilerCalls;

fn main() {
    if env::args().nth(1) == Some("-vV".to_owned()) {
        driver::catch_with_exit_code(move || {
            println!("RefinedRust {}", env!("RR_VERSION"));
            driver::run_compiler(&env::args().collect::<Vec<_>>(), &mut RRCompilerCalls {});
        })
        .exit_process();
    }

    if env::args().any(|s| s == "--show-config") {
        println!("Current detected configuration:");
        return print!("{}", rrconfig::dump());
    }

    driver::install_ice_hook(BUG_REPORT_URL, |_handler| ());

    // If we should act like rustc, just run the main function of the driver
    if rrconfig::be_rustc() {
        driver::main();
    }

    // otherwise, initialize our loggers
    env_logger::init();

    info!("Getting output dir: {:?}", env::var("RR_OUTPUT_DIR"));

    // This environment variable will not be set when building dependencies.
    let is_primary_package = env::var("CARGO_PRIMARY_PACKAGE").is_ok();
    info!("is_primary_package: {}", is_primary_package);
    // Is this crate a dependency when user doesn't want to verify dependencies
    let is_no_verify_dep_crate = !is_primary_package && !rrconfig::verify_deps();

    if is_no_verify_dep_crate {
        rrconfig::set_no_verify(true);
    }

    let mut rustc_args = vec![];
    let mut is_codegen = false;
    for arg in env::args() {
        // Disable incremental compilation because it causes mir_borrowck not to be called.
        if arg == "--codegen" || arg == "-C" {
            is_codegen = true;
        } else if is_codegen && arg.starts_with("incremental=") {
            // Just drop the argument.
            is_codegen = false;
        } else {
            if is_codegen {
                rustc_args.push("-C".to_owned());
                is_codegen = false;
            }
            rustc_args.push(arg);
        }
    }

    if !rrconfig::no_verify() {
        rustc_args.push("-Zalways-encode-mir".to_owned());
        rustc_args.push("-Zpolonius".to_owned());

        if rrconfig::check_overflows() {
            // Some crates might have a `overflow-checks = false` in their `Cargo.toml` to
            // disable integer overflow checks, but we want to override that.
            rustc_args.push("-Coverflow-checks=on".to_owned());
        }

        if rrconfig::dump_debug_info() {
            rustc_args.push(format!(
                "-Zdump-mir-dir={}",
                rrconfig::log_dir()
                    .unwrap()
                    .join("mir")
                    .to_str()
                    .expect("failed to configure dump-mir-dir")
            ));
            rustc_args.push("-Zdump-mir=all".to_owned());
            rustc_args.push("-Zdump-mir-graphviz".to_owned());
            rustc_args.push("-Zidentify-regions=yes".to_owned());
        }
        if rrconfig::dump_borrowck_info() {
            rustc_args.push("-Znll-facts=yes".to_owned());
            rustc_args.push(format!(
                "-Znll-facts-dir={}",
                rrconfig::log_dir()
                    .unwrap()
                    .join("nll-facts")
                    .to_str()
                    .expect("failed to configure nll-facts-dir")
            ));
        }
    }

    rrconfig::register_stdlib_paths();

    debug!("rustc arguments: {:?}", rustc_args);

    driver::catch_with_exit_code(move || {
        driver::run_compiler(&rustc_args, &mut RRCompilerCalls {});
    })
    .exit_process();
}

// From Prusti.
fn mir_borrowck(tcx: ty::TyCtxt<'_>, def_id: LocalDefId) -> queries::mir_borrowck::ProvidedValue<'_> {
    let bodies_with_facts = borrowck::consumers::get_bodies_with_borrowck_facts(
        tcx,
        def_id,
        borrowck::consumers::ConsumerOptions::PoloniusOutputFacts,
    );

    // NB the order of iteration doesn't matter here
    #[expect(clippy::iter_over_hash_type)]
    for (did, body) in bodies_with_facts {
        // SAFETY: This is safe because we are feeding in the same `tcx` that is
        // going to be used as a witness when pulling out the data.
        unsafe {
            translation::store_mir_body(tcx, did, body);
        }
    }

    let mut providers = query::Providers::default();
    borrowck::provide(&mut providers);
    let original_mir_borrowck = providers.mir_borrowck;
    original_mir_borrowck(tcx, def_id)
}

fn override_queries(_session: &session::Session, providers: &mut util::Providers) {
    // overriding these queries makes sure that the `mir_storage` gets all the relevant bodies
    providers.queries.mir_borrowck = mir_borrowck;
}

/// Main entry point to the frontend that is called by the driver.
/// This translates a crate.
pub fn analyze(tcx: ty::TyCtxt<'_>) {
    match translation::generate_coq_code(tcx, |vcx| vcx.write_coq_files()) {
        Ok(()) => (),
        Err(e) => {
            println!("Frontend failed with error {:?}", e);
            process::exit(1)
        },
    }

    if let Some(s) = rrconfig::post_generation_hook()
        && let Some(parts) = shlex::split(&s)
    {
        let work_dir = rrconfig::absolute_work_dir().unwrap();
        let dir_path = PathBuf::from(&work_dir);
        info!("running post-generation hook in {}: {:?}", dir_path.display(), s);

        let status = Command::new(&parts[0])
            .args(&parts[1..])
            .current_dir(&dir_path)
            .status()
            .expect("failed to execute process");
        println!("Post-generation hook finished with {status}");
    }

    if rrconfig::run_check() {
        if cfg!(target_os = "windows") {
            println!("Cannot run proof checker on Windows.");
        } else if let Some(dir_str) = rrconfig::output_dir() {
            let dir_path = PathBuf::from(&dir_str);

            info!("calling type checker in {}", dir_path.display());

            let status = Command::new("dune")
                .arg("build")
                .current_dir(&dir_path)
                .status()
                .expect("failed to execute process");

            println!("Type checker finished with {status}");
        }
    }
}

impl driver::Callbacks for RRCompilerCalls {
    fn config(&mut self, config: &mut interface::Config) {
        assert!(config.override_queries.is_none());
        if !rrconfig::no_verify() {
            let x: fn(&session::Session, &mut util::Providers) = override_queries;
            config.override_queries = Some(x);
        }
    }

    fn after_analysis(
        &mut self,
        _: &interface::interface::Compiler,
        tcx: ty::TyCtxt<'_>,
    ) -> driver::Compilation {
        if rrconfig::no_verify() {
            // TODO: We also need this to properly compile deps.
            // However, for deps I'd ideally anyways have be_rustc??
            return driver::Compilation::Continue;
        }

        // Analyze the crate and inspect the types under the cursor.
        analyze(tcx);

        driver::Compilation::Stop
    }
}
