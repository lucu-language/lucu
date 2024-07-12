{
  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  inputs.parcelr.url = "github:Astavie/parcelr";
  inputs.parcelr.inputs.nixpkgs.follows = "nixpkgs";

  outputs = { self, nixpkgs, parcelr }: 
    let
      supportedSystems = [ "x86_64-linux" "aarch64-linux" "x86_64-darwin" "aarch64-darwin" ];
      forEachSupportedSystem = f: nixpkgs.lib.genAttrs supportedSystems (system: f {
        pkgs = import nixpkgs {
          inherit system;
          overlays = [ parcelr.overlays.default ];
        };
      });
    in
    {
      devShells = forEachSupportedSystem ({ pkgs }: with pkgs; {
        default = pkgs.mkShell {

          packages = [
            ols
            php
          ];

          nativeBuildInputs = [
            odin
            pkgs.parcelr
          ];

        };
      });
    };
}
