{
  inputs.astapkgs.url = "github:Astavie/astapkgs";

  outputs = { self, astapkgs }: astapkgs.lib.package {

    package = pkgs: with pkgs; rustPlatform.buildRustPackage rec {
      src = ./.;
      name = "lucu";
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
    };

    devShell = pkgs: with pkgs; mkShell {

      buildInputs = [
        dev.rust-nightly
        libffi
        libxml2
        zlib
        ncurses
      ];

      LLVM_SYS_150_PREFIX = "${llvmPackages_15.libllvm.dev}";
      
    };
    
  } [ "x86_64-linux" ];
}
