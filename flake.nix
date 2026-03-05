{
  description = "Compact Sparse Merkle Trie for Aiken";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    haskell-mts.url = "github:paolino/haskell-mts/4cd37b80248b218e8f4c2fda8fc6a817e396a407";
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
