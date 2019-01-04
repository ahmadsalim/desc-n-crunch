{ nixpkgs ? <nixpkgs> }:
let
  pkgs = import nixpkgs {};
in
with pkgs; with idrisPackages; build-idris-package  {
  name = "descncrunch";
  version = "2017-11-15";

  idrisDeps = [ pruviloj ];

  src = ./.;

  meta = {
    description = "Descriptions, levitation, and reflecting the elaborator";
    homepage = https://github.com/ahmadsalim/desc-n-crunch;
    license = lib.licenses.gpl3;
    maintainers = [ lib.maintainers.brainrape ];
  };
}
