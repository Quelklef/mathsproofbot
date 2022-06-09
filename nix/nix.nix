{ pkgs ? import ./pkgs.nix }:

let

python = pkgs.python38.withPackages (ppkgs: with ppkgs; [ tweepy ]);

in
  { inherit python; }
