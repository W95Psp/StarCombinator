module StarCombinator.Core

module LP = FStar.List.Pure.Base
module L = FStar.List.Tot.Base
module H = StarCombinator.Helpers
module S = FStar.String

type parserErrorUnit = {
     start_pos: nat
   ; end_pos:   nat
   ; nature:    string
   ; message:   string
}
private
type parserErrorKind = | SeqErrKind | OrErrKind | UserErrKind : string -> parserErrorKind
type parserError = | ErrGroup : parserErrorKind -> list parserError -> parserError
                   | ErrUnit  : parserErrorUnit -> parserError

let canFlatten a b = match (a, b) with
  | (UserErrKind _, _) -> false
  | (_, UserErrKind _) -> false
  | (a, b) -> a = b

private
let rec goodOrder c0 = match c0 with
    | ErrUnit _           -> true
    | ErrGroup g0 children -> L.for_all (fun c -> (match c with
                 | ErrUnit _ -> true
                 | ErrGroup g1 _ -> not (canFlatten g0 g1)
                 ) && goodOrder (admit (); c)) children

let getFirstGroup e = match e with
                    | ErrUnit _ -> None
                    | ErrGroup g0 _ -> Some g0

//type parserError = e:parserError{goodOrder e}

let makeErrGroup group child =  true

(** Parsing a string might give a result (for instance a number, for a number parser), along with a position (i.e. where the parser stopped). It might also result in nothing (parsing "z" with a number parser would make nothing) **)

type parserResult a = | ParserRes : option (nat * a) -> parserError -> parserResult a
//type parserResult a = | ParserRes : option (nat  a -> parserResult a | NoRes : nat -> nat -> parserError -> parserResult a

(** A parser operates on a string which might have be already partially consumed: therefore, a parser takes the source string and a position **)
type parser a = string -> nat -> parserResult a

private
let ( @@ ) #a #b #c (g:b->c) (f:a->b) (v:a) = g (f v)
private
let ( @$ ) #a #b (f: a -> b) (x: a) = f x

private
let strToErr msg p0 p1 nature: parserError = ErrUnit ({start_pos = p0; end_pos = p1; nature = nature; message = msg})

let noError = strToErr "" 0 0 "NO_ERR"

let (<?>) #a (p:parser a) (msg:string) = fun source p0 -> let r = p source p0 in match r with
             | ParserRes None err -> ParserRes None (ErrGroup (UserErrKind msg) [err])
             | ParserRes _ _ -> r
            // | NoRes p1 p2 e0 -> NoRes p0 p2 @$ ErrGroup (UserErrKind msg) [e0]
               
let undefErr = strToErr ""

//private
//let bind #t #u (x:parserResult t) (f: (nat*t) -> (nat*u)): parserResult u
//    = match x with | ParserRes (Some (a, b)) errs -> ParserRes (Some @$ f (a, b)) errs
//                   | ParserRes None errs -> ParserRes None errs // | NoRes p0 p1 r -> NoRes #u p0 p1 r


private
let haveNoResult (ParserRes x _) = x == None
private
let haveSomeResult x = ~(haveNoResult x)


private
let bind #t #u (x:parserResult t) (f: (x:parserResult t{haveSomeResult x}) -> (x:parserResult u)): parserResult u
    = match x with | ParserRes (Some (a, b)) errs -> f x
                   | ParserRes None errs -> ParserRes None errs // | NoRes p0 p1 r -> NoRes #u p0 p1 r

let map_pr #t #u (x: parserResult t) (f: t -> u): parserResult u
    = x <-- x; let ParserRes (Some (p, v)) errs = x in
      ParserRes (Some (p, f v)) errs //(p, (f r))

private
let max (x y: nat) = if x >= y then x else y

let combine_no_res (ParserRes None e:(x:_{haveNoResult x})) (ParserRes None e':(x:_{haveNoResult x}))
                   = let f (x: parserError)//: (r: list parserError
                           //{L.for_all (fun (o: parserError) -> (not (ErrGroup? o) || (let ErrGroup gg _ = o in gg <> OrErrKind))) r})
                         = (match x with | ErrGroup OrErrKind c -> c | _ -> [x]) in
                     let l = f e @ f e' in
                     ParserRes None (ErrGroup OrErrKind l)
                   
let greedy_or #a #b (p_a: parser a) (p_b: parser b) : parser (either a b) = fun src pos -> 
  let r_a = p_a src pos in
  let r_b = p_b src pos in
  match (r_a, r_b) with
    | (ParserRes None _, ParserRes None _) -> combine_no_res r_a r_b
    | (value, ParserRes None _) -> map_pr value Inl
    | (ParserRes None _, value) -> map_pr value Inr
    | (val0, val1) -> let h #a (ParserRes (Some (x, _)) _:(r:parserResult a{haveSomeResult r})) = x in
                     if h val0 > h val1 then
                          map_pr val0 Inl           
                     else map_pr val1 Inr

let nongreedy_or #a #b (p_a: parser a) (p_b: parser b) : parser (either a b) = fun src pos -> 
  let r_a = p_a src pos in
  match r_a with
    | ParserRes _ _ -> map_pr r_a Inl
    | _ -> let r_b = p_b src pos in (
    match r_b with
      | ParserRes _ _ -> map_pr r_b Inr
      | _ -> combine_no_res r_a r_b
    )

let fp #a #b (f: a -> b) (p:parser a): parser b = fun src pos -> map_pr (p src pos) f

let (<|>) #a (p_a p_b: parser a) = fp (fun x -> match x with | Inl v -> v | Inr v -> v) (nongreedy_or p_a p_b)

let (<||>) #a (p_a p_b: parser a) = fp (fun x -> match x with | Inl v -> v | Inr v -> v) (greedy_or p_a p_b)

let recallOtherErrors a b = (ErrGroup SeqErrKind @$ [a;b])

let (<*>) #a #b (p_a: parser a) (p_b: parser b) : parser (a*b) = 
  let h = fun src pos ->
    res_a <-- p_a src pos; let ParserRes (Some (ap, av)) aerrs = res_a in
    res_b <-- p_b src pos; let ParserRes (Some (bp, bv)) berrs = res_b in
    (ParserRes (Some (bp, (av, bv))) @$ recallOtherErrors aerrs berrs)
  in fun src p0 -> let r = h src p0 in match r with
                 | ParserRes None err -> ParserRes None (ErrGroup SeqErrKind @$ (match err with
                         | ErrGroup SeqErrKind c -> c
                         | _ -> [err]))
                 | _ -> r

let sequence #a (ps: list (parser a) {~ (ps == [])}): parser (list a) = let h::ps = ps in 
    L.fold_left (fun acc x -> fp (fun (old, n) -> old @ [n]) (acc <*> x)) (fp (fun x -> [x]) h) ps

let unexpected #a (msg: string) : (parser a) = fun _ pos ->
  ParserRes None (strToErr msg pos pos "unexpected")

let choice #a (ps: list @$ parser a {~(ps == [])}) : parser a = let (h::ps) = ps in
    L.fold_left (fun x y -> x <|> y) h ps

let many #a (p: parser a): parser (list a) = 
  let rec h (acc:list a) src pos =
    match p src pos with
      | ParserRes (Some (p, v)) errs -> admitP (p << p); (match h (L.append acc [v]) src p with
                                                        | ParserRes x e1 -> ParserRes x (recallOtherErrors errs e1))
      | ParserRes _ errs -> ParserRes (Some (pos, acc)) noError
  in h []

let many1 #a (p: parser a): parser (list a) = fp (fun (a, b) -> a::b) (p <*> many p)

let skipMany #a (p: parser a): parser unit = fp (fun _ -> ()) (many p)

let skipMany1 #a (p: parser a): parser unit = fp (fun _ -> ()) (many1 p)


let (<*>>) a b = fp (fun (_, b) -> b) (a <*> b)
let (<<*>) a b = fp (fun (a, _) -> a) (a <*> b)

let between #l #i #r (left:parser l) (right:parser r) (inner: parser i): parser i
    = left <*>> inner <<*> right

let maybe #a (p:parser a): parser (option a) = fun src pos -> match p src pos with
                | ParserRes (Some (x, y)) errs -> ParserRes (Some (x, (Some y))) errs
                | ParserRes _ errs -> ParserRes (Some (pos, None)) errs
                //| NoRes _ _ _ -> ParserRes pos None

let sepBy1 #a (inner: parser a) sep: parser (list a)
    = fp (fun (a,b) -> a :: b) (inner <*> many (sep <*>> inner))

let sepBy #a (inner: parser a) sep: parser (list a)
    = fp (fun x -> match x with | None -> [] | Some x -> x)
         (maybe @$ sepBy1 inner sep)

let endBy #a (inner:parser a) sep end_symb = sepBy inner sep <*> end_symb

let endBy1 #a (inner:parser a) sep end_symb = sepBy1 inner sep <*> end_symb

let lookAhead #a (ahead: parser a) = fun src pos ->
    let x = ahead src pos in match x with
    | ParserRes (Some (_, v)) _ -> ParserRes (Some (pos, v)) noError
    | _ -> x

let notFollowedBy #a (after: parser a) = fun src p0 ->
    let x = after src p0 in match x with
    | ParserRes (Some (p1, v)) _ -> ParserRes None (strToErr "not expected (notFollowedBy)" p0 p1 "not-followed-by")
    | _ -> ParserRes (Some (p0, ())) noError
    
let eof: parser unit = fun src pos -> if S.length src = pos
                                   then ParserRes (Some (pos, ())) noError
                                   else ParserRes None (strToErr "expected end of file" pos pos "eof")

private
let count_in_list (#a:eqtype) (x: a) (l: list a):nat = L.fold_left (fun (acc:nat) h -> acc + (if h = x then 0 else 1)) 0 l

private
let count_in_str ch (str: string) =
    let rec h (p:nat) = if p = 0 then 0 else let p = p - 1 in
                ((if S.get str p = ch then 1 else 0) + h p)
    in h (S.length str)
//private
//let unwrapParserError: parserError -> list (nat * string) = id 

// let rec filterErrs (err: parserError) (fg: parserErrorKind -> list parserError -> bool) (fu: parserErrorUnit -> bool) = match err with
//     | ErrGroup grp c -> fg grp (admit(); c) && L.for_all (fun e -> admitP (e << err); filterErrs e fg fu) (admit(); c)
//     | ErrUnit x -> fu x


let getBounds (err: parserError) =
  let min0 (x: option nat) (y: nat) = Some (match x with | None -> y | Some x -> min x y) in
  let max0 (x: option nat) (y: nat) = Some (match x with | None -> y | Some x -> max x y) in
  let z u = (match u with | (Some x, Some y) -> (x, y) | _ -> (0,0)) in
  let rec h (err: parserError): (nat * nat) = (match err with
    | ErrUnit x -> (x.start_pos, x.end_pos)
    | ErrGroup g c -> let x = L.map (admitP (err << err); h) c in
                     z (L.fold_left min0 None (L.map fst x), L.fold_left max0 None (L.map snd x)) 
    //let (p0, p1) = h err
  ) in h err

private
let rec l_filter #a (pred: a -> bool) (l: list a): list (r: a {pred r}) = match l with
  | [] -> []
  | h::t -> let next = l_filter pred t in if pred h then h::next else next 

let catOptions #a (l: list (option a)) =
  let l': list (r:option a {Some? r}) = l_filter (fun x -> Some? x) l in
  L.map (fun ((Some x):(r:option a {Some? r})) -> x) l'

let rec onlySmall (err: parserError): option parserError = 
  let p0, p1 = getBounds err in
  if p1 - p0 > 20 then (match err with
    | ErrGroup SeqErrKind c -> let l: list parserError = catOptions (L.map (admitP (err << err); onlySmall) c) in
                              if L.length l = 0 then None else Some (ErrGroup (UserErrKind "Shortened sequence") l)
    | _ -> None
  ) else Some err

let replaceCharStr all ch str = S.concat "" (L.map (fun c -> if c = ch then str else S.string_of_list [c]) @$ S.list_of_string all)

let identLines str ident = S.concat "" (L.map (fun c -> if c = '\n' then "\n" ^ ident else S.string_of_list [c]) @$ S.list_of_string str)

let showUnitError (src: string) (ident: string) ({ start_pos; end_pos; nature; message }): string =
    let err_len: nat = admit(); end_pos - start_pos in
    let err_len = if err_len = 0 then 1 else err_len in
    let s_before = S.substring src 0 start_pos in
    let s_middle = S.substring src start_pos err_len in
    let s_after  = S.substring src (start_pos+err_len) (S.length src - start_pos - err_len) in
    let errStyle = H.underline @@ H.fail in
    let line_num = count_in_str '\n' s_before in
    "\n" ^ ident ^ H.fail "Parser error " ^ " on line "^ H.underline (string_of_int line_num) ^ " [pos:"^string_of_int start_pos^"-"^string_of_int end_pos^"]:" ^
    "\n" ^ ident ^ identLines (s_before ^ errStyle s_middle ^ s_after) ident ^
    "\n" ^ ident ^ "Reason: " ^ message

let groupToString group = match group with
    | UserErrKind str -> str
    | SeqErrKind -> "sequence"
    | OrErrKind -> "or"

let rec showGroupError (src: string) (ident: string) (err: parserError{ErrGroup? err}): Tot string
    = let ErrGroup grp cl = err in
      if (not (UserErrKind? grp)) && (L.length cl = 1) then (let [x] = cl in (admitP (src << src); showError) src ident x)
      else (
        let p0, p1 = getBounds err in
        showUnitError src ident ({start_pos = p0; end_pos = p1; nature = "group"; message = groupToString grp})
      ^ "\n\n" ^ ident ^ H.bold "More particulary:"
      ^ S.concat ("\n" ^ ident) (L.map (admit(); showError src (ident ^ "\t")) cl)
      )
and showError (src: string) ident (err: parserError): Tot string = match err with | ErrGroup _ _ -> showGroupError src ident (admit(); err) | ErrUnit x -> showUnitError src ident x 

private
let rec lst_contains #a (f: a -> a -> bool) (x: a) (l: list a) = match l with
  | [] -> false | h::t -> f x h || lst_contains f x t

let rec err_eq a' b = match a' with
  | ErrUnit a -> (match b with 
    | ErrUnit b -> a.start_pos = b.start_pos && a.message = b.message && a.end_pos = b.end_pos
    | _ -> false)
  | ErrGroup ga a -> (match b with 
    | ErrGroup gb b -> ga = gb && L.length a = L.length b && L.for_all (fun (a,b) -> admitP(a << a'); err_eq a b) (LP.zip a b)
    | _ -> false)
    
let remove_dups (l:list parserError) = 
    let rec h l already: Tot (list parserError) (decreases l) = match l with
    | [] -> []
    | hd::tl -> if lst_contains err_eq hd already then h tl already else hd::(h tl (hd::already)) 
    in h l []

let rec isErrNonEmpty err = match err with
  | ErrUnit x -> x.message <> ""
  | ErrGroup _ c -> L.for_all (admitP (err << err); isErrNonEmpty) c
let rec filterEmpty err = 
  let f = L.filter (fun c -> match c with
    | ErrUnit v ->  v.message <> ""
    | ErrGroup (UserErrKind _) _ -> true
    | ErrGroup _ c -> L.length c > 0
    ) in
  match err with
  | ErrGroup g cl -> ErrGroup g @$ remove_dups @$ f @$ 
               L.map (admitP (err << err); filterEmpty) @$ f cl
  | _ -> err

let make #a (p: parser a): string -> either a string = fun src -> match (p <<*> (eof <?>  "make function expects end of file at the end of the source")) src 0 with
   | ParserRes (Some (_, res)) _ -> Inl res
   | ParserRes _ error -> Inr @$ (
     let error = filterEmpty (match onlySmall error with | None -> error | Some x -> x) in
     showError src "" error ^ "\n\n\n" ^ replaceCharStr src '\n' "[JUMP-LINE]" ^ "\n\nlen is " ^ string_of_int (S.length src) ^ "\n"
     // S.concat "\n\n\n" @$ L.map (showError src) @$ L.filter (fun (_,x) -> x <> " ") errors
   ) 
