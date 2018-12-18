module StarCombinator.Base

open StarCombinator.Core
open StarCombinator.Operators
open FStar.String
open FStar.Char

module H = StarCombinator.Helpers
module C = StarCombinator.Constants
module L = FStar.List.Tot.Base
module M = FStar.Mul

let exact (exactChar: char) : parser char
    = satisfy_char (fun c -> c = exactChar) <?> "expected '" ^ string_of_list [exactChar] ^ "'"

private
let showRange r = String.concat "" (L.map (fun x -> match x with
                                               | '\n' -> "\\n"
                                               | '\t' -> "\\t"
                                               |  ch  -> string_of_list [ch]
                                         ) r)

let oneOf (possibles: list char): parser char
    = satisfy_char (fun c -> H.lst_contains c possibles) <?> "expected something in the range [" ^ showRange possibles ^ "]"

let noneOf (possibles: list char): parser char
    = satisfy_char (fun c -> not (H.lst_contains c possibles)) <?> "expected something out of the range ["^showRange possibles^"]"

let space = oneOf ('\n'::C.isSpaceChar)

 (* zero one or more spaces *)
let spaces: parser unit = fp (fun _ -> ()) (many space)

let newline = fp (fun _ -> ()) (exact '\n')
let crlf = fp (fun _ -> ()) (exact '\r' <*> newline)

let endOfLine = newline <|> crlf

let tab =fp (fun _ -> ()) (exact '\t')

let lower = oneOf C.lowerCaseCharList
let upper = oneOf C.upperCaseCharList

let digit = oneOf C.digitList

//let charClass (l:list char {~(l == [])}): parser char = choice (L.map exact l)

let digit_num : parser (n: nat{n <= 9}) = 
  let convert (c:char): (n: nat{n <= 9}) = match c with
              | '1' -> 1 | '2' -> 2 | '3' -> 3 | '4' -> 4 | '5' -> 5
              | '6' -> 6 | '7' -> 7 | '8' -> 8 | '9' -> 9 |  _  -> 0 in
  fp convert (oneOf C.digitList) <?> "expected digit"

let notLetter = (satisfy_char (fun c -> H.lst_contains c C.anyCaseCharList) <|> fp (fun _ -> ' ') eof) <?> "expected something different than a letter"

let letter = oneOf C.anyCaseCharList <?> "expected letter"

let natural_number : parser nat =
  let rec convert (c:list (n: nat{n <= 9})): nat = match c with
    | [] -> 0
    | hd::tl -> hd + (M.op_Star 10 (convert tl))
  in
  fp (fun x -> convert (L.rev x)) (many1 digit_num <<*> notFollowedBy letter) <?> "expected natural number"

let number: parser int = fp (fun ((m, n): (option char*nat)) -> match m with | Some _ -> 1 | None -> n)
                       (maybe (exact '-') <*> natural_number) <?> "expected number"


let alphaNum = oneOf (C.digitList @ C.anyCaseCharList) <?> "expected alphanumeric"

let hexDigit = oneOf (C.digitList @ list_of_string "ABCDEFabcdef") <?> "expected hex digit"

let sequence #a (lp: list (parser a) {~(lp == [])}) = let (hd::lp) = lp in
    L.fold_left (fun (acc: parser (list a)) (y: parser a) -> fp (fun (l, v) -> l @ [v]) (acc <*> y)) (fp (fun x -> [x]) hd) lp

let exact_string (str:string{str <> ""}): parser string = fp string_of_list (sequence #char (admitP(list_of_string str <> []); L.map exact (list_of_string str))) <?> "expected the exact string \""^str^"\""

let string_satisfy (fchar: char -> bool): parser string = fp string_of_list (many1 (satisfy_char fchar)) <?> "expected some string maching some predicate"

let word: parser string = (string_satisfy (fun c -> H.lst_contains c C.anyCaseCharList) <<*> notFollowedBy letter) <?> "expected a word"

let keyword str: parser unit = fp (fun _ -> ()) (ptry (spaces <*> exact_string str) <*> spaces <<*> notFollowedBy letter) <?> "expected the keyword "^str

let keywords (lstr: list string{lstr<>[]}): parser unit = fp (fun _ -> ()) (sequence #string (admit(); L.map (fun s -> spaces <*>> exact_string s) lstr) <*> spaces) <?> "expected the keywords " ^ (String.concat " " lstr)

let ckwd ch: parser unit = (spaces <<*> exact ch <<*> spaces) <?> "expected char keyword "^(String.string_of_list [ch])

let wrapspace p = spaces <*>> p <<*> spaces

let match_boolean_litterate = ((fp (fun x -> true) (exact_string "true")) <|> (fp (fun x -> false) (exact_string "false"))) <?> "expected false or true"

let between l r i = l <*>> i <<*> r

let between_kwd l r i = between (keyword l) (keyword r) i <?> "expected something of the form \""^l^" ... "^r^"\""

let sepBy1 i s = (fun (v,l) -> v::l) `fp` i <*> (many (s <*> i))
let sepBy i s = ptry ((fun (v,l) -> v::l) `fp` (i <*> (many (s <*>> i)))) <|> fp (fun x -> [x]) i

let match_list l r s i = between_kwd l r (sepBy i (keyword s)) <?> "expected a list \""^l^" ... "^s^" ... "^r^"\""

