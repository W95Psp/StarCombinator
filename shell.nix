let
  native_caml = ["MyIO.ml"];
  includes = [];
  pkgs = import <nixpkgs> {};
  fstar = pkgs.fstar;
  outfile = "program";
  ocaml_packages = ["fstarlib" "fstar-tactics-lib" "fstar-compiler-lib"];
  fstar-bin = "${fstar}/bin/fstar.exe";
  no-extract = [ "FStar.BitVector" "MyIO" "FStar.List.Tot" "FStar.List.Tot.Properties" "FStar.Math.Lemmas" "FStar.Math.Lib" "FStar.OrdSet" "FStar.PredicateExtensionality" "FStar.Preorder" "FStar.PropositionalExtensionality" "FStar.Reflection" "FStar.Reflection.Const" "FStar.Reflection.Derived" "FStar.Reflection.Derived.Lemmas" "FStar.Reflection.Formula" "FStar.Seq" "FStar.Seq.Base" "FStar.Seq.Properties" "FStar.StrongExcludedMiddle" "FStar.Tactics" "FStar.Tactics.Derived" "FStar.Tactics.Effect" "FStar.Tactics.Logic" "FStar.Tactics.PatternMatching" "FStar.Tactics.Typeclasses" "FStar.Tactics.Util" "FStar.UInt"];
  h = pre: list: builtins.concatStringsSep " " (map (x: pre + " " + x) list);
in
pkgs.stdenv.mkDerivation rec {
  name = "shell-env";
  buildInputs = with pkgs.ocamlPackages; [
    pkgs.ocaml
    ocamlbuild findlib ppx_deriving pprint ppx_deriving_yojson zarith stdint batteries
     (pkgs.writeScriptBin "compile" ''
     #!${pkgs.stdenv.shell}
     source ${findlib.setupHook}
     ${shellHook}
     
     rm -f .depend *.checked
     rm -rf out/
     mkdir -p out/
     ${builtins.concatStringsSep " && " (map (x: "cp " + x + " out/") native_caml)}


	   ${fstar-bin} ${h "--no_extract" no-extract} --odir out --codegen OCaml StarCombinator.Examples.fst
      
  	 cd out
     ocamlbuild -package ${builtins.concatStringsSep "," ocaml_packages} "StarCombinator_Examples.native"
     cp ./StarCombinator_Examples.native ../${outfile}
     cd ..
	   # cd out && ./StarCombinator_Examples.native
     '')
  ];
  shellHook = "addOCamlPath ${pkgs.fstar}";
}
  
