module StarCombinator.Core

module LP = FStar.List.Pure.Base
module L = FStar.List.Tot.Base
module S = FStar.String

open StarCombinator.Helpers

open MyIO

private
let remove_dups (#a:eqtype) (l:list a) = 
    let rec h l already: Tot (list a) (decreases l) = match l with
    | [] -> []
    | hd::tl -> if lst_contains hd already then h tl already else hd::(h tl (hd::already)) 
    in h l []


type map key value = list (key * list value)
let get (#tk:eqtype) #tv (map:map tk tv) (key: tk): list tv =
  let rec h l = match l with | [] -> [] | (hd, lvals)::tl -> (if hd = key then lvals else h tl) in
  h map
  
let set (#tk:eqtype) (#tv:eqtype) (map:map tk tv) (key: tk) (value: tv) =
  let rec h l = match l with
                | [] -> [(key, [value])]
                | (hd, lvals)::tl -> (if hd = key
                                    then ((hd, (if lst_contains value lvals then lvals else value::lvals))::tl)
                                    else ((hd, lvals)::(h tl))
                                    )
  //let rec h l = match l with | [] -> [] | (hd, lvals)::tl -> (hd, (if hd = key then value::lvals else lvals))::tl
  in h map
  
let merge (#tk:eqtype) (#tv:eqtype) (map0:map tk tv) (map1:map tk tv) =
  let rec h l = match l with | [] -> map0 | (k,vl)::tl -> let map2 = h tl in L.fold_left (fun m v -> set m k v) map2 vl
  in h map1

type parserState = {
    position: nat
  ; maximum_position: nat
  ; errors: map (nat * nat) string
  ; source: string
  ; nest_level: nat
}
    
let (+++) (s1 s2: parserState): (nat -> nat -> nat) -> parserState = fun f -> 
                  { position = f s1.position s2.position
                  ; maximum_position = max s1.maximum_position s2.maximum_position
                  ; errors = merge s1.errors s2.errors
                  ; source = s1.source
                  ; nest_level = s1.nest_level
                  }

type parserDescription = {
    message: string
}

noeq
type parser a = {
    description: unit -> parserDescription
  ; parser_fun: string -> parserState -> (parserState * option a)
}

private
let rec mkIdent (n: nat) =
  if n = 0 then "" else "  " ^ mkIdent (n - 1)

let add_error s0 p0 p1 message = {s0 with errors = set s0.errors (p0, p1) message}

private
let p2fun #a (p: parser a): (parserState -> (parserState * option a)) = fun x -> (
    let d = (p.description ()).message in
    //let t = mi_unsafe_now () in
    //let _ = mi_debug_print_string ("\n"^mkIdent x.nest_level^"Start "^d^" at "^(S.substring x.source x.position 1)) in
    let (s1, r) = p.parser_fun d x in
    //let t = mi_unsafe_now () - t in
    //let _ = mi_debug_print_string ("\n"^mkIdent x.nest_level^"End "^d^". Time(ms)= "^string_of_int t) in
    let s2 = {s1 with nest_level = s1.nest_level + 1} in
    let s3 = if None? r then add_error s2 x.position s2.position (p.description ()).message else s2 in
    (s3, r)
  )

//let p2fun a = fun x -> let x = mi_debug_print_string "Start" a.parser_fun (a.description ()) x

let mktup2 a b = (a, b) 

let fp #a #b (f: a -> b) (p:parser a): parser b
  = { description = p.description
    ; parser_fun = fun sd s0 -> let (s1, r) = p.parser_fun sd s0 in (s1, f <$> r)
    }

let mk_d msg = fun _ -> {message = msg}
let cat_d a b = fun _ -> {message = (a ()).message ^ (b ()).message}

let mk_seq #a #b (parser1: parser a) (parser2: parser b): parser (a * b) = {
    description = (mk_d "sequence")//(fun _ -> "( " ^ parser2.description () ^ " . " ^ parser1.description () ^ " )")
  ; parser_fun  = (let run sd (s0: parserState): (parserState*option (a * b)) = (
                     let (s1, r1) = (p2fun parser1) s0 in
                     match r1 with
                     | None -> (add_error s1 s0.position s1.position sd, None)
                     | Some r1 -> 
                       let (s2, r2) = (p2fun parser2) s1 in
                       (let s3 = (s1 +++ s2) (fun _ p2 -> p2) in (match r2 with
                       | None ->  (add_error s3 s0.position s2.position sd, None)
                       | Some r2 -> (s3, Some (r1, r2))
                       ))
                      // (s1 +++ s2) (fun _ p2 -> p2), mktup2 r1 <$> r2
                  ) in run)
}

let choice_two #a #b (parser1: parser a) (parser2: parser b): parser (either a b) = {
    description = (mk_d "or")//"( " ^ parser2.description () ^ " | " ^ parser1.description () ^ " )")
  ; parser_fun  = (let run _ (s0: parserState): (parserState * option (either a b)) = (
                     let (s1, r1) = (p2fun parser1) s0 in
                     match r1 with
                     | None -> if s1.position <> s0.position
                              then (s0 +++ s1) (fun a b -> max a b), None
                              else let (s2, r2) = (p2fun parser2) s0 in
                                   (s1 +++ s2) (fun _ p2 -> p2), (Inr <$> r2)
                     | Some r1 -> s1, (Some (Inl r1))
                  ) in run)
}

let choice_two_same p1 p2 = fp (fun x -> match x with | Inl y -> y | Inr y -> y) (choice_two p1 p2)


let empty parser unit = {
    description = (mk_d "empty")
  ; parser_fun  = (let rec run sd (s0: parserState) = (s0, Some ()) in run)
}

let choice #a (lp: list (parser a) {~(lp == [])}): parser a = match lp with
                 | hd::lp -> L.fold_left (fun acc p -> choice_two_same acc p) hd lp

let maybe #a (p: parser a): parser (option a) = {
    description = ((mk_d "?") `cat_d` p.description)
  ; parser_fun  = (let run _ (s0: parserState): (parserState * option (option a)) = (
                     let (s1, r1) = (p2fun p) s0 in
                     (s1, Some r1)
                  ) in run)
}

let map_error #a (p: parser a) (msg: string): parser a = {description = (mk_d msg); parser_fun = p.parser_fun }

let delayMe #a (p: unit -> parser a): parser a = {description = (fun () -> (p ()).description ()); parser_fun = fun sd st0 -> let x = p () in x.parser_fun sd st0}

let many #a (p: parser a): parser (list a) = {
    description = (mk_d "[" `cat_d` p.description `cat_d` mk_d "]")
  ; parser_fun  = (let rec run sd (s0: parserState): (r:(parserState * option (list a)) {Some? (snd r)}) = (
                     let (s1, r1) = (p2fun p) s0 in
                     match r1 with
                     | None -> (s1, Some [])
                     | Some r1 -> let (s2, Some r2) = admitP (s1 << s0); run sd s1 in (s2, Some (r1::r2))
                  ) in run)
}

let many1 #a (p: parser a) = (fun (a, b) -> a::b) `fp` (p `mk_seq` many p)

let eof: (parser unit) = {
    description = (mk_d "EOF")
  ; parser_fun  = (let rec run sd (s0: parserState) = if s0.position = S.length s0.source then (s0, Some ())
                                                      else (add_error s0 s0.position s0.position sd, None) in run)
}

let notFollowedBy #a (p:parser a): parser unit = {
    description = (p.description `cat_d` mk_d " was not expected")
  ; parser_fun  = (let rec run sd (s0: parserState) =
                  let (s1, res) = (p2fun p) s0 in
                  (match res with
                  | None   -> (s0, Some ())
                  | Some _ -> (add_error s0 s0.position s1.position sd, None)
                  )
                in run)
}

let lookAhead #a (p:parser a): parser a = {
    description = (mk_d "lookAhead(" `cat_d` p.description `cat_d` mk_d ")")
  ; parser_fun  = (let rec run sd (s0: parserState) =
                  let (s1, res) = (p2fun p) s0 in
                  (match res with
                  | Some v -> (s0, Some v)
                  | None   -> ((s0 +++ s1) (fun a b -> b), None)
                  )
                in run)
}

let ptry #a (p:parser a): parser a = {
    description = (mk_d "try(" `cat_d` p.description `cat_d` mk_d ")")
  ; parser_fun  = (let rec run sd (s0: parserState) =
                  let (s1, res) = (p2fun p) s0 in
                  (match res with
                  | Some v -> (s1, Some v) // when everything goes well, "ptry p == p"
                  | None   -> ((s0 +++ s1) (fun a b -> a), None) // in case of failure, we aknowledge the error, but place the cursor at s0.position (then no tokens were consumed)
                  )
                in run)
}

let satisfy_char (f: String.char -> bool) = 
  let d = "satisfy_char(some function)" in {
    description = (mk_d d)
  ; parser_fun = fun sd s0 -> let ch = S.get s0.source s0.position in if f ch
                          then ({s0 with position = s0.position + 1}, Some ch)
                          else (add_error s0 s0.position (s0.position + 1) d, None) 
  }

let exact_char ch = satisfy_char (fun ch' -> ch = ch')
let neg_satisfy_char f = satisfy_char (fun ch -> not (f ch))

private
let get_errors_tup3 (errors: map (nat * nat) string): list (nat * nat * string) =
  let rec h errors = match errors with
    | [] -> []
    | ((p0, p1), msgs)::tl -> let rec i msgs = (match msgs with
              | [] -> []
              | msg::tl -> (p0, p1, msg)::i tl
              ) in (i msgs) @ h tl
  in h errors

let gt_errors ((p0, p1, _): (nat * nat * _)) ((p0', p1', _): (nat * nat * _)): bool =
  if      p1 > p1' then true
  else if p1 = p1' then p0 > p0'
  else                  false

let sort_errors (errors: list (nat * nat * string)): list (nat * nat * string) 
  = L.sortWith (L.compare_of_bool gt_errors) errors

private
let count_in_list (#a:eqtype) (x: a) (l: list a):nat = L.fold_left (fun (acc:nat) h -> acc + (if h = x then 0 else 1)) 0 l

private
let count_in_str ch (str: string) =
    let rec h (p:nat) = if p = 0 then 0 else let p = p - 1 in
                ((if S.get str p = ch then 1 else 0) + h p)
    in h (S.length str)

let replaceCharStr all ch str = S.concat "" (L.map (fun c -> if c = ch then str else S.string_of_list [c]) (S.list_of_string all))

let identLines str ident = S.concat "" (L.map (fun c -> if c = '\n' then "\n" ^ ident else S.string_of_list [c]) (S.list_of_string str))


let make p = fun (source: string) ->
  let s0 = { position = 0
           ; maximum_position = 0
           ; errors = []
           ; source = source
           ; nest_level = 0
           } in let (s1, res) = (p2fun p) s0 in
           match res with
           | Some res -> Inl res
           | None -> Inr (
             let l = sort_errors (get_errors_tup3 s1.errors) in
             let show ((p0, p1, msg):(nat*nat*string)): string =
               let src = s1.source in
               let err_len: nat = admit(); p1 - p0 in
               let err_len = if err_len = 0 then 1 else err_len in
               let s_before = S.substring src 0 p0 in
               let s_middle = S.substring src p0 err_len in
               let s_after  = S.substring src (p0+err_len) (S.length src - p0 - err_len) in
               let errStyle = fun x -> underline (fail x) in
               let ident = "" in
               let line_num = count_in_str '\n' s_before in
               "\n" ^ ident ^ fail "Parser error " ^ " on line "^ underline (string_of_int line_num) ^ " [pos:"^string_of_int p0^"-"^string_of_int p1^"]:" ^
               "\n" ^ ident ^ identLines (s_before ^ errStyle s_middle ^ s_after) ident ^
               "\n" ^ ident ^ "Reason: " ^ msg 

             in
             S.concat "\n" (L.map show l) 
           )
