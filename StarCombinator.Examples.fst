module StarCombinator.Examples

open StarCombinator
open MyIO

open FStar.Mul
open StarCombinator.Examples.While


let op_add = (fun x y -> x + y)
let op_minus = (fun x y -> x - y)

let calculator_parser: parser int = 
    let rec h (_:unit): parser int = (
      //let g = number in
      let g = delayMe (admitP (() << ()); h) in
      (ptry
        (
          (fun ((a, op), b) -> a `op` b) @<<
          (number <*> (
                (op_add   *<< ((keyword "+"  <|> keyword "plus") <?> "expected + or plus"))
              <|> (op_minus *<< ((keyword "minus" <|> keyword "-") <?> "expected - or minus"))
          ) <*> g)
        )
      )<|> number
      //    fp (fun (a, b) -> a + b) (number <<*> (keyword "plus" <|> ckwd '+') <*> g)
      //<|> fp (fun (a, b) -> a - b) (number <<*> (keyword "minus"<|> keyword "-") <*> g)
      //<|> fp (fun (a, b) -> a * b) (number <<*> (keywords ["hey";"times"] <|> keyword "*") <*> g)
      //<|> number
    //and no_lrec () =
    //       number
    //  <|> (keyword "Bonjour" <*>> number <<*> keywords ["X";"Y";"Z"])
    ) in (h ()) <<*> eof
    
let calculator source = match (make calculator_parser) source with
  | Inl intvalue -> "Got some result: " ^ string_of_int intvalue
  | Inr error -> "Got some error: " ^ error

// module All = FStar.All
// module S = FStar.String

// let mi_input_lines (): All.ML string =
//   let rec h (): All.ML (list string) =
//     let line = mi_input_line () in
//     if line = "" then [line]
//     else (h ())@[line]
//   in let r = h () in
//   S.concat "\n" r

// let x = make lFakeInstr_parser
//let delayMe #a (p: unit -> parser a): parser a = {description = (fun _ -> "x"); parser_fun = fun sd st0 -> let x = p () in x.parser_fun sd st0}

let rec tiny' () = (
  fp (fun (l, num) -> string_of_int num ^ "  " ^ String.concat " " (FStar.List.Tot.Base.map (fun (a,b) -> String.string_of_list [a;b]) l)) 
  (
    (many (exact_char 'c' <*> (exact_char '!' <|> exact_char 'a'))) <*> number// <<*> (admitP (() << ()); delayMe tiny')
  )
)
let tiny = make (tiny' ())
 
let main0 () = 
  let prog = mi_input_line () in
  mi_print_string (match tiny prog with
    | Inl x -> "Youpi:" ^ x
    | Inr x -> x)
  
let main1 () = 
  let prog = mi_input_line () in
  mi_print_string (match calculator prog with
    | r -> r)


let main2 () = 
  let prog = mi_input_line () in
  mi_print_string (match (make (match_list "(" ")" "," aexp_parser <<*> eof)) prog with
    | Inl r -> String.concat ", " (List.map lAExpToString r)
    | Inr r -> r)


let main3 () = 
  let prog = mi_input_line () in
  mi_print_string (match (make ((
               hFunction @<< (
                   (keyword "function" <*>> word)
               <*> (match_list "(" ")" "," word <<*> keyword "{")
               <*> ((LFakeInstrSkip *<< number) <<*> keyword "}")
               )) <<*> eof)) prog with
    | Inl r -> lFakeInstrToString r
    | Inr r -> r)


let main4 () = 
  let prog = mi_input_line () in
  mi_print_string (match (make (lFakeInstr_parser <<*> eof)) prog with
    | Inl r -> lFakeInstrToString r
    | Inr r -> r)


let main = main4 ()

