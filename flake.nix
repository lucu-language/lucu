{
  description = "A Nix-flake-based Rust development environment";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-24.05";
  };

  outputs = { self, nixpkgs }:
    let
      supportedSystems = [ "x86_64-linux" "aarch64-linux" "x86_64-darwin" "aarch64-darwin" ];
      forEachSupportedSystem = f: nixpkgs.lib.genAttrs supportedSystems (system: f {
        pkgs = import nixpkgs { inherit system; };
      });
    in
    {
      packages = forEachSupportedSystem ({ pkgs }: {

        default = pkgs.rustPlatform.buildRustPackage {
          name = "lucu";
          src = ./.;
          cargoLock = {
            lockFile = ./Cargo.lock;
            allowBuiltinFetchGit = true;
          };
          buildInputs = with pkgs; [
            libffi
            libxml2
            zlib
            ncurses
          ];
          LLVM_SYS_180_PREFIX = "${pkgs.llvmPackages_18.libllvm.dev}";
          LUCU_CORE = ./.;
        };

      });
      devShells = forEachSupportedSystem ({ pkgs }: {

        default = pkgs.mkShell {
          packages = with pkgs; [
            # compilation
            rustc
            cargo
            clippy
            bacon
            openssl
            pkg-config
            cargo-deny
            cargo-edit
            cargo-watch
            rust-analyzer
            rustfmt

            # runtime
            wabt
            wasmtime
            pkgsCross.mingwW64.buildPackages.gcc
            lld_15
          ];

          buildInputs = with pkgs; [
            libffi
            libxml2
            zlib
            ncurses
          ];
          
          LLVM_SYS_180_PREFIX = "${pkgs.llvmPackages_18.libllvm.dev}";
          LUCU_CORE = ./.;
        };
      });
    };
}
