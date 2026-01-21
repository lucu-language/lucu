{ pkgs, ... }:

{
  packages = [
    pkgs.bacon pkgs.cargo-watch
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
