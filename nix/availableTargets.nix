{
  pkgs,
  rust-overlay,
}: desiredComponents:
with pkgs.lib;
let
  toolchain = rust-overlay.lib._internal.defaultManifests.nightly.latest.pkg;
  getArch = pkg: attrNames toolchain.${pkg}.target;
in foldl' intersectLists (getArch (head desiredComponents)) (map getArch (tail desiredComponents))
