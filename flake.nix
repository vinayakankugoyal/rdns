{
  description = "rdns - a caching, blocklisting DNS forwarder with a TUI";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  };

  outputs = { self, nixpkgs }:
    let
      systems = [ "x86_64-linux" "aarch64-linux" "x86_64-darwin" "aarch64-darwin" ];
      forAllSystems = f: nixpkgs.lib.genAttrs systems (system: f nixpkgs.legacyPackages.${system});
      cargoToml = builtins.fromTOML (builtins.readFile ./Cargo.toml);

      mkRdns = pkgs: pkgs.rustPlatform.buildRustPackage {
        pname = "rdns";
        version = cargoToml.package.version;

        src = pkgs.lib.cleanSource ./.;
        cargoLock.lockFile = ./Cargo.lock;

        meta = with pkgs.lib; {
          description = "A caching, blocklisting DNS forwarder with Prometheus metrics and a TUI";
          homepage = "https://github.com/vinayakankugoyal/rdns";
          license = licenses.mit;
          mainProgram = "rdns";
        };
      };
    in
    {
      packages = forAllSystems (pkgs: rec {
        rdns = mkRdns pkgs;
        default = rdns;
      });

      apps = forAllSystems (pkgs: {
        default = {
          type = "app";
          program = pkgs.lib.getExe (mkRdns pkgs);
        };
      });

      checks = forAllSystems (pkgs: {
        build = mkRdns pkgs;
      });

      devShells = forAllSystems (pkgs: {
        default = pkgs.mkShell {
          inputsFrom = [ (mkRdns pkgs) ];
          packages = with pkgs; [
            rustfmt
            clippy
            rust-analyzer
          ];
        };
      });
    };
}
