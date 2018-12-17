module StarCombinator

open FStar.String
open FStar.Char

module M = FStar.Mul
module L = FStar.List.Tot.Base
module T = FStar.Tactics

//include StarCombinator.Constants
include StarCombinator.Core
include StarCombinator.Base

(* delayMe makes a parser act "lazy", then you can define recursive parsers (hopefully!) *)
let delayMe #a (p: unit -> parser a): parser a = fun a b -> (p ()) a b

(*
let match_stringf (f: char -> bool) : parser string = repeat (match_charf f) string_of_list

let sequence #a #b #c (p_a: parser a) (p_b: parser b) (f: a -> b -> c) : parser c = fun src pos ->
  r_a <-- p_a src pos;
  r_b <-- p_b src (fst r_a);
  ParserRes (fst r_b) (f (snd r_a) (snd r_b))

let match_string #a (str: string) (symb: a): parser a = fun src pos -> (L.fold_left (fun c char -> sequence c (match_char () char) (fun _ _ -> symb)) (match_empty symb) (list_of_string str)) src pos

let (<*>) #t1 #t2 (a:parser t1) (b:parser t2): parser (t1*t2) = sequence a b (fun a b -> (a, b))
let (<|>) = fun a b -> comb_or a b (fun e -> match e with | Inl x -> x | Inr x -> x)

let match_class #a (choices: list char) (symb: char -> a): parser a = fun src pos ->
  let p = L.fold_left (fun c char -> c <|> (match_char (Some char) char)) (match_empty None) choices in
  p <-- p src pos;
  (match snd p with
  | Some v -> ParserRes (fst p) (symb v)
  | None -> NoRes)

let match_digit : parser (n: nat{n <= 9}) = 
  let convert (c:char): (n: nat{n <= 9}) = match c with
              | '1' -> 1 | '2' -> 2 | '3' -> 3 | '4' -> 4 | '5' -> 5
              | '6' -> 6 | '7' -> 7 | '8' -> 8 | '9' -> 9 |  _  -> 0 in
  match_class digitList convert

let match_nat : parser nat =
  let rec convert (c:list (n: nat{n <= 9})): nat = match c with
    | [] -> 0
    | hd::tl -> hd + (M.op_Star 10 (convert tl))
  in
  repeat match_digit (convert @ L.rev)

let fp #a #b (f: a -> b) (p:parser a): parser b = fun src pos -> map_pr (p src pos) f

private
let letterList = upperCaseCharList `L.append` lowerCaseCharList

let match_letter = match_class letterList id

let match_word = repeat match_letter string_of_list


let match_space = match_class [' ';'\t';'\n';'\r'] (fun _ -> ())
let match_any_spaces = repeat match_space (fun _ -> ())

let match_eof: parser unit = fun src pos -> if pos >= String.length src then ParserRes pos () else NoRes 
let match_eol: parser unit = match_char () '\n'

let match_comment: parser string = match_any_spaces <*>> match_string "//" () <*>> match_stringf (fun x -> x <> '\n')

let wrapspace #a (p: parser a): parser a = match_any_spaces <*>> p <<*> match_any_spaces 

let opc ch: parser unit = wrapspace (match_char () ch)

let match_keyword str: parser unit = wrapspace (match_string str ())
let match_keywords (strs:list string{L.length strs > 0}): parser unit = 
  let hd::tl = strs in
    L.fold_left (fun c kw -> c <*>> match_keyword kw) (match_keyword hd) tl 

let match_maybe #a (p:parser a): parser (option a) = fun src pos -> match p src pos with
                | ParserRes x y -> ParserRes x (Some y)
                | NoRes -> ParserRes pos None

let match_comments: parser (option (list string)) = match_maybe (repeat match_comment (fun l -> l))

let match_list #a (left:string) (right:string) (inner: parser a): parser (list a)
    = wrapspace (match_keyword left <*>> (
                            (fp (fun (x, l) -> x :: l)
                              (inner <*> repeat (match_keyword ", " <*>> inner) id)
                            )
                       <<*> match_empty ([] <: list string)
                 ) <<*> match_keyword right)

// TODO: *supposing _left_ and _right_ always define blocks of code*, cut the program according to theses, and restrict _inner_ to the computed blocks
// this idea breaks with comments or strings
// good idea would be to pre-process the whole program first, listing all blocks first
//let match_brackets #a (left:string) (right:string) (inner: parser a): parser (list a)
//    = 


let match_boolean_litterate: parser bool = match_any_spaces <*>> match_string "true" true <|> match_string "false" false <<*> match_any_spaces

let close_parser parser src = match (parser <<*> match_eof) src 0 with
  | ParserRes _ res -> Some res
  | NoRes -> None
  
*)
