# Lean toolchain only — stay in this directory.
{ pkgs ? import <nixpkgs> { } }:

pkgs.mkShell {
  packages = [ pkgs.elan ];
  shellHook = ''
    export PATH="$HOME/.elan/bin:${pkgs.elan}/bin:$PATH"
  '';
}
