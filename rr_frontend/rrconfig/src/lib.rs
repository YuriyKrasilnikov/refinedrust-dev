// © 2025, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

#![feature(normalize_lexically)]

use std::path::{NormalizeError, PathBuf};
use std::process::Command;
use std::sync::{LazyLock, RwLock, RwLockWriteGuard};
use std::{env, fmt, path};

use serde::{Deserialize, Serialize, de};

fn vec_or_split_colon<'de, D>(d: D) -> Result<Vec<String>, D::Error>
where
    D: de::Deserializer<'de>,
{
    struct V;

    impl<'de> de::Visitor<'de> for V {
        type Value = Vec<String>;

        fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
            formatter.write_str("string with ':' or list of strings")
        }

        fn visit_str<E>(self, v: &str) -> Result<Self::Value, E>
        where
            E: de::Error,
        {
            Ok(v.split(':').map(ToOwned::to_owned).collect())
        }

        fn visit_string<E>(self, v: String) -> Result<Self::Value, E>
        where
            E: de::Error,
        {
            Ok(v.split(':').map(ToOwned::to_owned).collect())
        }

        fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
        where
            A: de::SeqAccess<'de>,
        {
            let mut out = Vec::new();
            while let Some(elem) = seq.next_element::<String>()? {
                out.push(elem);
            }
            Ok(out)
        }
    }

    d.deserialize_any(V)
}

#[derive(Deserialize, Serialize)]
#[serde(default)]
#[expect(clippy::struct_excessive_bools)]
struct Config {
    be_rustc: bool,
    log_dir: String,
    check_overflows: bool,
    dump_debug_info: bool,
    dump_borrowck_info: bool,
    skip_unsupported_features: bool,
    spec_hotword: String,
    attribute_parser: String,
    run_check: bool,
    verify_deps: bool,
    no_verify: bool,
    no_assumption: bool,
    admit_proofs: bool,
    generate_dune_project: bool,
    #[serde(deserialize_with = "vec_or_split_colon")]
    lib_load_paths: Vec<String>,
    work_dir: String,
    output_dir: Option<String>,
    post_generation_hook: Option<String>,
    extra_specs: Option<String>,
    trust_debug: bool,
    find_stdlib: bool,
}

impl Default for Config {
    fn default() -> Self {
        Self {
            be_rustc: false,
            log_dir: "./log/".to_owned(),
            check_overflows: true,
            dump_debug_info: false,
            dump_borrowck_info: false,
            skip_unsupported_features: true,
            spec_hotword: "rr".to_owned(),
            attribute_parser: "verbose".to_owned(),
            run_check: false,
            verify_deps: false,
            no_verify: false,
            no_assumption: false,
            admit_proofs: false,
            generate_dune_project: true,
            lib_load_paths: vec![],
            work_dir: ".".to_owned(),
            output_dir: None,
            post_generation_hook: None,
            extra_specs: None,
            trust_debug: false,
            find_stdlib: true,
        }
    }
}

static SETTINGS: LazyLock<RwLock<Config>> = LazyLock::new(|| {
    // RwLock due to `rustc` parallelism
    RwLock::new({
        let mut builder = config::Config::builder();

        // 1. Read the optional TOML file "RefinedRust.toml", if there is any
        builder = builder.add_source(config::File::with_name("RefinedRust.toml").required(false));

        // 2. Override with an optional TOML file specified by the `RR_CONFIG` env variable
        if let Ok(file) = env::var("RR_CONFIG") {
            // set override for workdir to the config file path
            let path_to_file = PathBuf::from(file.clone());
            let filepath = path_to_file.parent().unwrap().to_str().unwrap();

            builder = builder.set_default("work_dir", filepath).unwrap();
            builder = builder.add_source(config::File::with_name(&file));
        }

        // 3. Override with env variables (`RR_QUIET`, ...)
        builder = builder.add_source(config::Environment::with_prefix("RR").ignore_empty(true));

        // 4. Fill empty fields with default values
        let config: Config = builder.build().unwrap().try_deserialize().unwrap();

        config
    })
});

/// Makes the path absolute with respect to the `work_dir`.
fn make_path_absolute(path: String) -> Result<PathBuf, NormalizeError> {
    let path_buf = PathBuf::from(path);
    if path_buf.is_absolute() {
        return path_buf.normalize_lexically();
    }

    let work_dir_buf = PathBuf::from(work_dir());
    if work_dir_buf.is_absolute() {
        return work_dir_buf.join(path_buf).normalize_lexically();
    }

    path::absolute(work_dir_buf.join(path_buf)).unwrap().normalize_lexically()
}

/// Retrieve paths of `RefinedRust`'s stdlib, using Nix (`RR_NIX_STDLIB`) or opam (`refinedrust-stdlib`)
fn find_stdlib_paths() -> Vec<String> {
    if let Ok(nix_path) = env::var("RR_NIX_STDLIB") {
        return vec![nix_path];
    }

    let Ok(output) = Command::new("opam").args(["config", "list", "refinedrust-stdlib"]).output() else {
        return vec![];
    };

    if !output.status.success() {
        return vec![];
    }

    let Some(ocaml_path) = String::from_utf8_lossy(&output.stdout)
        .lines()
        .find(|line| line.starts_with("refinedrust-stdlib:share"))
        .and_then(|line| line.split_whitespace().nth(1))
        .map(String::from)
    else {
        return vec![];
    };

    vec![ocaml_path]
}

pub fn register_stdlib_paths() {
    access_config(|mut c| {
        if c.find_stdlib {
            c.lib_load_paths.extend(find_stdlib_paths());
        }
    });
}

fn access_config<'a, T, C: FnOnce(RwLockWriteGuard<'a, Config>) -> T>(callback: C) -> T {
    callback(SETTINGS.write().unwrap())
}

/// Retrieve the TOML configuration
#[must_use]
pub fn dump() -> String {
    access_config(|c| toml::to_string(&*c).unwrap())
}

/// Should refinedrust-rustc behave like rustc?
#[must_use]
pub fn be_rustc() -> bool {
    access_config(|c| c.be_rustc)
}

/// In which folder should we store log/dumps?
pub fn log_dir() -> Result<PathBuf, NormalizeError> {
    make_path_absolute(access_config(|c| c.log_dir.clone()))
}

/// Should we check for overflows?
#[must_use]
pub fn check_overflows() -> bool {
    access_config(|c| c.check_overflows)
}

/// Should we dump debug files?
#[must_use]
pub fn dump_debug_info() -> bool {
    access_config(|c| c.dump_debug_info)
}

/// Should we dump borrowck info?
#[must_use]
pub fn dump_borrowck_info() -> bool {
    access_config(|c| c.dump_borrowck_info)
}

/// Skip features that are unsupported or partially supported
#[must_use]
pub fn skip_unsupported_features() -> bool {
    access_config(|c| c.skip_unsupported_features)
}

/// The hotword with which specification attributes should begin.
#[must_use]
pub fn spec_hotword() -> String {
    access_config(|c| c.spec_hotword.clone())
}

/// Which attribute parser to use? Currently, only the "verbose" parser is supported.
#[must_use]
pub fn attribute_parser() -> String {
    access_config(|c| c.attribute_parser.clone())
}

/// Run the proof checker after generating the Coq code?
#[must_use]
pub fn run_check() -> bool {
    access_config(|c| c.run_check)
}

/// Should also dependencies be verified?
#[must_use]
pub fn verify_deps() -> bool {
    access_config(|c| c.verify_deps)
}

/// Should verification be skipped?
#[must_use]
pub fn no_verify() -> bool {
    access_config(|c| c.no_verify)
}

pub fn set_no_verify(value: bool) {
    access_config(|mut c| c.no_verify = value);
}

/// Whether to allow specification to be assumed
#[must_use]
pub fn no_assumption() -> bool {
    access_config(|c| c.no_assumption)
}

/// Whether to admit proofs of functions instead of running Qed.
#[must_use]
pub fn admit_proofs() -> bool {
    access_config(|c| c.admit_proofs)
}

/// Whether to generate a dune-project file for this project
#[must_use]
pub fn generate_dune_project() -> bool {
    access_config(|c| c.generate_dune_project)
}

/// Get the paths in which to search for `RefinedRust` library declarations.
#[must_use]
pub fn lib_load_paths() -> Vec<PathBuf> {
    access_config(|c| c.lib_load_paths.clone())
        .into_iter()
        .map(make_path_absolute)
        .filter_map(Result::ok)
        .collect()
}

#[must_use]
fn work_dir() -> String {
    access_config(|c| c.work_dir.clone())
}

pub fn absolute_work_dir() -> Result<PathBuf, NormalizeError> {
    make_path_absolute(work_dir())
}

/// Which directory to write the generated Coq files to?
#[must_use]
pub fn output_dir() -> Option<PathBuf> {
    access_config(|c| c.output_dir.clone()).map(make_path_absolute).and_then(Result::ok)
}

/// Post-generation hook
#[must_use]
pub fn post_generation_hook() -> Option<String> {
    access_config(|c| c.post_generation_hook.clone())
}

/// Which file should we read extra specs from?
#[must_use]
pub fn extra_specs_file() -> Option<PathBuf> {
    access_config(|c| c.extra_specs.clone()).map(make_path_absolute).and_then(Result::ok)
}

/// Should we automatically trust `fmt::Debug` trait impls?
#[must_use]
pub fn trust_debug() -> bool {
    access_config(|c| c.trust_debug)
}

#[cfg(test)]
#[expect(clippy::bool_assert_comparison)]
mod tests {
    use std::sync::Once;

    use super::*;

    // These tests MUST use different keys for each test.
    // The same SETTINGS variable is used throughout.

    // There is a race between `std::env::set_var()` and `SETTINGS`.
    static SETUP_ENV: Once = Once::new();

    fn setup<F: FnOnce(RwLockWriteGuard<'_, Config>)>(test: F) {
        SETUP_ENV.call_once(|| {
            // Safety: This block is single-threaded
            #[expect(clippy::multiple_unsafe_ops_per_block)]
            unsafe {
                env::set_var("RR_log_dir", "12345");
                env::set_var("RR_ChEcK_oVeRfLoWs", "false");
                env::set_var("RR_dump_debug_info", "1");
            }
        });

        access_config(test);
    }

    #[test]
    fn read_default() {
        setup(|c| assert_eq!(c.be_rustc, false));
    }

    #[test]
    fn read_env_str() {
        setup(|c| assert_eq!(c.log_dir.clone(), "12345"));
    }

    #[test]
    fn read_env_bool() {
        setup(|c| assert_eq!(c.check_overflows, false));
    }

    #[test]
    fn read_env_int_as_bool() {
        setup(|c| assert_eq!(c.dump_debug_info, true));
    }

    #[test]
    fn write() {
        setup(|mut c| c.admit_proofs = true);
        setup(|c| assert_eq!(c.admit_proofs, true));

        setup(|mut c| c.admit_proofs = false);
        setup(|c| assert_eq!(c.admit_proofs, false));
    }

    #[test]
    fn write_multiple() {
        setup(|mut c| c.skip_unsupported_features = false);
        setup(|c| assert_eq!(c.skip_unsupported_features, false));

        setup(|mut c| c.spec_hotword = "12345".to_owned());
        setup(|c| assert_eq!(c.spec_hotword, "12345"));
    }
}
