{
  description = "CDCL SAT solver in python";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    with flake-utils.lib;
    eachSystem allSystems (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        py = pkgs.python3.withPackages (p: with p; [
          numpy
        ]);
      in rec {
        devShell = pkgs.mkShell {
          nativeBuildInputs = with pkgs; [
            py
          ];
        };
      });
}

