{ pkgs ? import <nixpkgs> {} }:

let

inherit (import ./nix/nix.nix { inherit pkgs; }) python;

in pkgs.mkShell {
  buildInputs = [ python ];
}
