{
  description = "A core language for rule-based hardware design";

  inputs = {
    flake-utils.url = "github:numtide/flake-utils";
    makes.url = "github:fluidattacks/makes/24.02";
    nixpkgs.url = "github:nixos/nixpkgs/release-24.05";

    # unicoq.url = "git+file:///home/samxamnam/Projects/unicoq?ref=flake";
  };

  outputs =
    { self
    , flake-utils
    , makes
    , nixpkgs
      # , unicoq
    , ...
    }:
      with flake-utils.lib;
      eachDefaultSystem
        (system:
        let
          pkgs = import nixpkgs {
            inherit system;
            overlays = [
              self.overlays.default
              # unicoq.overlays.default 
            ];
          };
        in
        {
          checks = {
            koika = self.packages.${system}.default.override {
              doCheck = true;
            };
          };

          devShells.default = self.checks.${system}.koika;

          packages = {
            default = self.packages.${system}.coq8_18-koika;
            coq8_18-koika = pkgs.coqPackages_8_18.koika;
            coqDev-koika = pkgs.coqPackages_koika.koika;
          };

          apps.makes = makes.apps.${system}.default;
        })
      // {
        # NOTE: To use this flake, apply the following overlay to nixpkgs and use
        # koika from its respective coqPackages_VER attribute set!
        overlays.default = import ./overlay.nix;
      };
}
