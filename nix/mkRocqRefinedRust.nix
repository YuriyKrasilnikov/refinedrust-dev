{
  cargoRefinedRust,
  pkgs,
  rrPkgs,
}: {
  libDeps ? [],
  opam-name ? pname,
  pname,
  propagatedBuildInputs ? [],
  src,
  useDune ? true,
  withStdlib ? true,
  withTheories ? false,
  cargoRefinedRustArgs ? {},
  rocqArgs ? {},
  rocqTheoriesArgs ? {},
  ...
} @ origArgs: let
  args = let
    fullArgs = origArgs // {inherit cargoRefinedRustArgs libDeps opam-name propagatedBuildInputs rocqArgs rocqTheoriesArgs src useDune withTheories;};
    commonRemoveAttrs = ["cargoRefinedRustArgs" "pname" "propagatedBuildInputs" "rocqArgs" "rocqTheoriesArgs" "withTheories"];
  in rec {
    cargo = builtins.removeAttrs fullArgs (commonRemoveAttrs ++ ["opam-name" "useDune"]);
    rocq = builtins.removeAttrs fullArgs (commonRemoveAttrs ++ ["cargoArtifacts" "cargoExtraArgs" "cargoVendorDir" "libDeps" "src" "target" "withStdlib"]);
    rocqTheories = builtins.removeAttrs rocq ["opam-name"];
  };

  theories = pkgs.rocqPackages.mkRocqDerivation ({
      src = "${src}/theories";
      propagatedBuildInputs =
        (pkgs.lib.optionals withStdlib [rrPkgs.stdlib])
        ++ libDeps
        ++ propagatedBuildInputs;

      pname = "refinedrust-" + pname + "-theories";
      opam-name = opam-name + "-theories";
    }
    // args.rocqTheories // rocqTheoriesArgs);
in
  pkgs.rocqPackages.mkRocqDerivation ({
      src = cargoRefinedRust (args.cargo // cargoRefinedRustArgs);
      pname = "refinedrust-" + pname;

      propagatedBuildInputs =
        (pkgs.lib.optionals withStdlib [rrPkgs.stdlib])
        ++ libDeps
        ++ propagatedBuildInputs
        ++ (pkgs.lib.optionals withTheories [theories]);

      postInstall = let
        name = pkgs.lib.replaceStrings ["-" "_"] ["/" "/"] pname;
      in ''
        mkdir -p $out/share/${name}
        find . -name "interface.rrlib" -exec cp {} $out/share/${name}/. \;
      '';
    }
    // args.rocq // rocqArgs)
