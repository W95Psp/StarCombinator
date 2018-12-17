module StarCombinator.Examples

open StarCombinator
open MyIO

open FStar.Mul
open StarCombinator.Examples.While

let calculator_parser: parser int = 
    let rec h (_:unit): parser int = (
      let g = delayMe (admit (); h) in
          fp (fun (a, b) -> a + b) (number <<*> (keyword "plus" <|> ckwd '+') <*> g)
      <|> fp (fun (a, b) -> a - b) (number <<*> (keyword "minus"<|> keyword "-") <*> g)
      <|> fp (fun (a, b) -> a * b) (number <<*> (keywords ["hey";"times"] <|> keyword "*") <*> g)
      <|> number
    //and no_lrec () =
    //       number
    //  <|> (keyword "Bonjour" <*>> number <<*> keywords ["X";"Y";"Z"])
    ) in h ()

let calculator source = match (make calculator_parser) source with
  | Inl intvalue -> "Got some result: " ^ string_of_int intvalue
  | Inr error -> "Got some error: " ^ error

module All = FStar.All
module S = FStar.String

let mi_input_lines (): All.ML string =
  let rec h (): All.ML (list string) =
    let line = mi_input_line () in
    if line = "" then [line]
    else (h ())@[line]
  in let r = h () in
  S.concat "\n" r

let x = make lFakeInstr_parser

let main0 () = 
  let prog = mi_input_line () in
  mi_print_string (match calculator prog with
    | r -> r)

let main1 () = 
  let prog = mi_input_lines () in
  mi_print_string (match x prog with
    | Inl _ -> "Succeeds!"
    | Inr r -> r)

let main = main0 ()
