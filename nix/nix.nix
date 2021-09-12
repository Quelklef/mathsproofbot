{ pkgs }:

let

python = pkgs.python36.withPackages (ppkgs: with ppkgs; [ tweepy ]);

in
  { inherit python; }
