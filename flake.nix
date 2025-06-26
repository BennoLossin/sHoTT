{
  description = "Devshell for sHoTT";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs?ref=nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    rzk.url = "github:rzk-lang/rzk";
  };

  outputs = inputs @ {
    self,
    nixpkgs,
    rzk,
    flake-utils,
    ...
  }:
    {
    }
    // flake-utils.lib.eachDefaultSystem (system: let
      pkgs = import nixpkgs {
        inherit system;
      };
    in {
      devShells = let
        pygments-rzk = pkgs.callPackage ./nix/pygments-rzk.nix {};
        mkdocs-plugin-rzk = pkgs.callPackage ./nix/mkdocs-plugin-rzk.nix {};
      in {
        default = pkgs.callPackage ./nix/shell.nix {
          inherit pygments-rzk mkdocs-plugin-rzk;
          rzk = rzk.packages.${system}.default;
        };
      };
    });
}
