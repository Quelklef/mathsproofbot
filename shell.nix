{ pkgs ? import ./nix/pkgs.nix }:

let

inherit (import ./nix/nix.nix { inherit pkgs; }) python;

in pkgs.mkShell {
  buildInputs = [ python ];

  shellHook = ''
      export MATHSPROOFBOT_AUTH=$(cat ${pkgs.writeText "auth" (import <secrets>).mathsproofbot-auth})
  '';
}
