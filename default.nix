{ pkgs ? import ./nix/pkgs.nix }:

let

inherit (import ./nix/nix.nix { inherit pkgs; }) python;

in pkgs.stdenv.mkDerivation {
  name = "mathsproofbot";
  src = ./src;
  installPhase = ''
    mkdir -p $out/py
    cp -r $src/. $out/py
    echo "${python}/bin/python $out/py/twitter.py \"\$@\"" > $out/run.sh
    chmod +x $out/run.sh
  '';
}
