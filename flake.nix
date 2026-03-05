{
  description = "Compact Sparse Merkle Trie for Aiken";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    haskell-mts.url = "github:paolino/haskell-mts/f0e2d220bbdd448a3ae2bbae068455c54e446eb5";
  };

  outputs =
    {
      nixpkgs,
      flake-utils,
      haskell-mts,
      ...
    }:
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        pkgs = nixpkgs.legacyPackages.${system};

        test-vectors = haskell-mts.packages.${system}.csmt-test-vectors;

        generate-vectors = pkgs.runCommand "csmt-test-vectors.ak" { } ''
          ${test-vectors}/bin/csmt-test-vectors > $out
        '';

      in
      {
        packages.test-vectors = generate-vectors;

        devShells.default = pkgs.mkShell {
          packages = [
            pkgs.aiken
            pkgs.just
          ];
        };
      }
    );
}
