{
  description = "Category theory in Wiz";

  inputs = {
    # The Wiz toolchain (wiz, grail, the standard library). flake.lock pins the commit;
    # `wiz-toolchain` names the same commit for tower users.
    wiz.url = "github:wiz-pl/wiz/aeaa34ef8527c2a72e703959742f7a99d9c03fc9";
    # The same nixpkgs as the toolchain, so its binaries are shared.
    nixpkgs.follows = "wiz/nixpkgs";
  };

  outputs = { self, nixpkgs, wiz }:
    let
      systems = [ "x86_64-linux" "aarch64-linux" ];
      forAll = f: nixpkgs.lib.genAttrs systems (system: f system nixpkgs.legacyPackages.${system});
    in {
      devShells = forAll (system: pkgs: {
        default = pkgs.mkShell {
          packages = [ wiz.packages.${system}.wiz ];   # wiz and grail
        };
      });
    };
}
