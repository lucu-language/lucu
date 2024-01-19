{
  inputs.astapkgs.url = "github:Astavie/astapkgs";

  outputs = { self, astapkgs }: astapkgs.lib.package rec {

    name = "lucu";

    package = pkgs: with pkgs; rustPlatform.buildRustPackage rec {
      inherit name;
      src = ./.;
      cargoLock = {
        lockFile = (src + "/Cargo.lock");
        allowBuiltinFetchGit = true;
      };
      buildInputs = [
        libffi
        libxml2
        zlib
        ncurses
      ];
      LLVM_SYS_150_PREFIX = "${llvmPackages_15.libllvm.dev}";
      LUCU_CORE = ./.;
    };

    devShell = pkgs: with pkgs; mkShell {

      buildInputs = [
        rustc
        cargo
        bacon
        rust-analyzer
        rustfmt
        clippy

        pkgsCross.mingwW64.buildPackages.gcc
        lld_15
        libffi
        libxml2
        zlib
        ncurses

        wabt
        wasmtime

        xorg.libxcb
      ];

      LLVM_SYS_150_PREFIX = "${llvmPackages_15.libllvm.dev}";
      
    };
    
  } [ "x86_64-linux" ];
}
