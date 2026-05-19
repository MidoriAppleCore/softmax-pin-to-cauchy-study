{
  description = "Lean + elan only (this folder). No Node — use mathgame’s flake for the web game.";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";

  outputs =
    { self, nixpkgs }:
    let
      systems = [ "x86_64-linux" "aarch64-linux" "aarch64-darwin" "x86_64-darwin" ];
      forAllSystems = nixpkgs.lib.genAttrs systems;
    in
    {
      devShells = forAllSystems (system: {
        default =
          let
            pkgs = import nixpkgs { inherit system; };
          in
          pkgs.mkShell {
            packages = [ pkgs.elan ];
            shellHook = ''
              export PATH="$HOME/.elan/bin:${pkgs.elan}/bin:$PATH"
              echo "transformers-are-cauchy-poisson: use \`lake\`/\`lean\` from elan (matches lean-toolchain)."
            '';
          };
      });
    };
}
