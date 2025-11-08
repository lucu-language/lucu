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
      "miri"
    ];
    enable = true;
  };

  git-hooks.hooks = {
    clippy.enable = true;
  };
}
