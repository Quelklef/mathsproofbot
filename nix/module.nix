{ pkgs
, auth ? builtins.readFile ../auth.json
}:

{
  systemd.services.mathsproofbot = {
    description = "mathsproofbot";
    after = [ "network.target" ];
    wantedBy = [ "default.target" ];
    script = ''
      export MATHSPROOFBOT_AUTH=$(cat /run/keys/mathsproofbot-auth)
      ${import ../default.nix { inherit pkgs; }}/run.sh --listen
    '';
    serviceConfig = {
      Type = "simple";
      Restart = "always";
    };
  };

  deployment.keys.mathsproofbot-auth.text = auth;
}
