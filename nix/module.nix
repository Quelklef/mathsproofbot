{ pkgs ? import ./pkgs.nix }:

{
  systemd.services.mathsproofbot = {
    description = "mathsproofbot";
    after = [ "network.target" ];
    wantedBy = [ "default.target" ];
    script = ''
      export MATHSPROOFBOT_AUTH=$(cat /run/keys/mathsproofbot-auth)
      export PYTHONUNBUFFERED=1  # suppress output buffering
      ${import ../default.nix { inherit pkgs; }}/run.sh --listen
    '';
    serviceConfig = {
      Type = "simple";
      Restart = "always";
    };
  };

  deployment.keys.mathsproofbot-auth.text = (import <secrets>).mathsproofbot-auth;
}
