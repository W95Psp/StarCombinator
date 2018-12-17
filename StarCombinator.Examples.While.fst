module StarCombinator.Examples.While

open StarCombinator

type lAExp =
  | LAExpLitt : int -> lAExp
  | LAExpVar  : string -> lAExp
  | LAExpPlus : lAExp  -> lAExp -> lAExp 
  | LAExpMinus: lAExp  -> lAExp -> lAExp 
  | LAExpMult : lAExp  -> lAExp -> lAExp
  | LAExpDiv  : lAExp  -> lAExp -> lAExp
type lBExp =
  | LBExpLitt: bool -> lBExp
  | LBExpNot : lBExp -> lBExp
  | LBExpAnd : lBExp -> lBExp -> lBExp
  | LBExpOr  : lBExp -> lBExp -> lBExp
  | LBExpEq  : lAExp -> lAExp -> lBExp
  | LBExpLe  : lAExp -> lAExp -> lBExp
type lInstrAssignable = | AssignLAExp : lAExp -> lInstrAssignable
                        | AssignCall  : string -> list lAExp -> lInstrAssignable
type lFakeInstr =
  | LFakeInstrAssign : string -> lInstrAssignable -> lFakeInstr
  | LFakeInstrSkip   : lFakeInstr
  | LFakeInstrSeq    : lFakeInstr -> lFakeInstr -> lFakeInstr
  | LFakeInstrIf     : lBExp -> lFakeInstr -> lFakeInstr -> lFakeInstr
  | LFakeInstrWhile  : lBExp -> lFakeInstr -> lFakeInstr
  | LFakeInstrFunDef : funFakeDef -> lFakeInstr
and funFakeDef = | FunFakeDef : string -> list string -> lFakeInstr -> funFakeDef


private
let uncurry f x = let (l,r) = x in f l r
private
let uncurry3 f x = let ((a,b),c) = x in f a b c

let aexp_parser: parser lAExp =
  let rec no_rec (): parser lAExp = fp LAExpLitt number <||> fp LAExpVar word
                   <||> (keyword "(" <*>> (admitP (() << ()); delayMe h') <<*> keyword ")")
  and h' (): parser lAExp = admitP (() << ()); let h = delayMe h' in
         no_rec () <||> fp (uncurry LAExpPlus)  (no_rec () <<*> ckwd '+' <*> h)
                   <||> fp (uncurry LAExpMinus) (no_rec () <<*> ckwd '-' <*> h)
                   <||> fp (uncurry LAExpMult)  (no_rec () <<*> ckwd '*' <*> h)
                   <||> fp (uncurry LAExpDiv)  (no_rec () <<*> ckwd '/' <*> h)
  in wrapspace (h' ())

let bexp_parser: parser lBExp =
  let rec no_rec (): parser lBExp = fp LBExpLitt (wrapspace match_boolean_litterate)
           <||> fp (uncurry LBExpEq) (aexp_parser <<*> exact_string "=="  <*> aexp_parser)
           <||> fp (uncurry LBExpLe) (aexp_parser <<*> exact_string "<="  <*> aexp_parser)
           <||> fp LBExpNot (exact '~' <*>> (admitP (() << ()); delayMe no_rec))
           <||> (between (keyword "(") (keyword ")") (delayMe h'))
  and h' (): parser lBExp = admitP (() << ()); let h = delayMe h' in
    no_rec () <||> fp (uncurry LBExpAnd) (no_rec () <<*> exact_string "&&" <*> h)
              <||> fp (uncurry LBExpOr)  (no_rec () <<*> exact_string "||" <*> h)
  in wrapspace (h' ())

let rec lFakeInstrIsWF prog toplevel = match prog with 
  | LFakeInstrSeq a b -> lFakeInstrIsWF a toplevel && lFakeInstrIsWF b toplevel 
  | LFakeInstrIf  _ a b -> lFakeInstrIsWF a false && lFakeInstrIsWF b false 
  | LFakeInstrWhile _ a -> lFakeInstrIsWF a false
  | LFakeInstrFunDef (FunFakeDef _ _ a) -> if toplevel then lFakeInstrIsWF a false else false 
  | _ -> true
type lFakeInstrWF = r:lFakeInstr {lFakeInstrIsWF r true}

let hAssignCall var fName args = LFakeInstrAssign var (AssignCall fName args)
let hAssignExp var exp = LFakeInstrAssign var (AssignLAExp exp) 

let match_comment: parser string = spaces <*>> keyword "//" <*>> string_satisfy (fun x -> x <> '\n')
let match_comments: parser (list string) = fp (fun x -> match x with | Some x -> x | None -> []) (maybe (many match_comment))

let lFakeInstr_parser: parser (r:lFakeInstr) =
   let z #a (arg:parser a) = arg <<*> match_comments in
   let rec no_rec (tl:bool): parser (r:lFakeInstr) = admitP (() << ()); z (
           fp (uncurry hAssignExp) (word <<*> keyword "=" <*> aexp_parser)
       <||> fp (uncurry3 hAssignCall) (word <<*> keyword "="
              <*> word <*> match_list "(" ")" "," aexp_parser)
       <||> fp (fun _ -> LFakeInstrSkip) (exact_string "SKIP")
       <||> fp (uncurry3 LFakeInstrIf) (
                  ((keywords ["if"; "("] <*>> bexp_parser) <<*> keywords [")"; "{"])
              <*> ((delayMe (h' false)) <<*> keywords ["}";"else";"{"])
              <*> ((delayMe (h' false)) <<*> keyword "}")
           )
       <||> fp (fun ((str,args),body) -> LFakeInstrFunDef (FunFakeDef str args body)) (
                  (keyword "function" <*>> word <*> 
                    (match_list "(" ")" "," word)
                    <<*> keyword "{")
              <*> (delayMe (h' false) <<*> keyword "}")
           )       
       <||> fp (uncurry LFakeInstrWhile) (
                  ((keywords ["while";"("] <*>> bexp_parser) <<*> keywords [")";"{"])
              <*> ((delayMe (h' false)) <<*> keyword "}")
           ))
   and h' (tl:bool) (): parser (r:lFakeInstr) = admitP (() << ()); let h = delayMe (h' tl) in
     z (
       no_rec tl <||> fp (uncurry LFakeInstrSeq) (no_rec tl <<*> keyword ";" <*> (match_comments <*>> h))
                 <||> (no_rec tl <<*> keyword ";")
     )
   in wrapspace (h' true ())
