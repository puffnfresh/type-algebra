let pkgs = import <nixpkgs> { };
in
pkgs.mkShell {
  buildInputs = [
    (pkgs.haskellPackages.ghcWithPackages (p: [ p.invariant p.hedgehog p.lens ]))
    pkgs.cabal-install
    pkgs.ghcid
    pkgs.hlint
  ];
}
