{ pkgs, ... }:

{
  packages = [
    pkgs.bacon pkgs.cargo-watch
    # dependencies of llvm at compile time
    pkgs.libffi pkgs.libxml2 pkgs.zlib
    # dependencies of lucu at runtime
    pkgs.lld_21
  ];

  languages.rust = {
    channel = "nightly";
    components = [
      "cargo"
      "rust-src"
      "rustc"
      "rustfmt"
      "clippy"
      "rust-analyzer"
    ];
    enable = true;
  };

  env.LLVM_SYS_211_PREFIX = "${pkgs.llvmPackages_21.libllvm.dev}";

  git-hooks.hooks = {
    # rustfmt.enable = true;
    # clippy.enable = true;
    tests = {
      enable = true;
      entry = "cargo test";
      files = "\\.(rs|lucu)$";
      pass_filenames = false;
    };
  };
}
