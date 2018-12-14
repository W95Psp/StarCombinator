module ParserCombinators

open FStar.String
open FStar.Char

module M = FStar.Mul
module L = FStar.List.Tot.Base
module T = FStar.Tactics

let lowerCaseCharList = list_of_string "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
let upperCaseCharList = list_of_string "abcdefghijklmnopqrstuvwxyz"
let digitList = list_of_string "1234567890"
let isSpecialChar = list_of_string "~@#$%^?!+-*<>\\/|&=:"

(** Parsing a string might give a result (for instance a number, for a number parser), along with a position (i.e. where the parser stopped). It might also result in nothing (parsing "z" with a number parser would make nothing) **)
type parserResult a = | ParserRes : nat -> a -> parserResult a | NoRes

(** A parser operates on a string which might have be already partially consumed: therefore, a parser takes the source string and a position **)
type parser a = string -> nat -> parserResult a

(** Identity for parsers, in a sense **)
let match_empty #a (symb: a) : parser a = fun _ pos -> ParserRes pos symb

(** if ch is matched, it output symb  **)
let match_char #a (symb: a) (ch: char) : parser a
    = fun src pos -> if pos >= FStar.String.length src then NoRes
                      else (
                         if get src pos = ch then ParserRes (pos+1) symb
                         else                     NoRes
                      )

(* if the next character ch satisfyies the predicate f, succeeds with ch *)                        
let match_charf (f: char -> bool) : parser char
  = fun src pos -> if pos >= FStar.String.length src then NoRes
                else (let ch = get src pos in
                      if f ch then  ParserRes (pos+1) ch 
                      else    NoRes
                )

private
let bind x f = match x with | ParserRes a b -> f (a, b) | _ -> NoRes

let map_pr x f = x <-- x; let (p, r) = x in ParserRes p (f r)

private
let fst' #a (x: parserResult a{ParserRes? x}) = match x with | ParserRes a _ -> a

private
let ( @ ) #a #b #c (g:b->c) (f:a->b) (v:a) = g (f v)

let comb_or #a #b #c (p_a: parser a) (p_b: parser b) (f: (either a b) -> c) : parser c = fun src pos -> 
  let r_a = p_a src pos in
  let r_b = p_b src pos in
  match (r_a, r_b) with
    | (NoRes, NoRes) -> NoRes
    | (value, NoRes) -> map_pr value (f @ Inl)
    | (NoRes, value) -> map_pr value (f @ Inr)
    | (val0 , val1 ) -> if (fst' val0) > (fst' val1) then
                            map_pr val0 (f @ Inl)           
                       else map_pr val1 (f @ Inr)

private
let rec repeat' #a (p_a: parser a) (acc:list a) src pos = 
  match p_a src pos with
    | ParserRes p v -> admitP (p << p); repeat' p_a (L.append acc [v]) src p
    | NoRes -> ParserRes pos acc

let repeat #a #b (p_a: parser a) (f: list a -> b) : parser b = fun src pos -> match repeat' p_a [] src pos with
    | ParserRes p v -> ParserRes p (f v)
    | NoRes -> NoRes

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

private
let uncurry f x = let (l,r) = x in f l r
private
let uncurry3 f x = let ((a,b),c) = x in f a b c
private
let delayMe #a (p: unit -> parser a): parser a = fun a b -> (p ()) a b

let (<*>>) a b = sequence a b (fun _ b -> b)
let (<<*>) a b = sequence a b (fun a _ -> a)

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

private
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
  
