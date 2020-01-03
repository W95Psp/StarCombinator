  { name = "StarCombinator";
    sources-directory = ./.;
    sources = [
      "MyIO"
      "StarCombinator.Base"
      "StarCombinator.Constants"
      "StarCombinator.Core"
      "StarCombinator.Examples"
      "StarCombinator.Examples.While"
      "StarCombinator"
      "StarCombinator.Helpers"
      "StarCombinator.Operators"
    ];
    ocaml-sources = [
      "MyIO.ml"
    ];
    dependencies = [];
    compile = [{
      module = "StarCombinator.Examples";
      assets = [];
      binary-name = "StarCombinator_example_bin";
    }];
  }
