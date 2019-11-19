module StarCombinator.Examples.While

open StarCombinator

module L = FStar.List.Tot.Base

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

let rec lAExpToString x = match x with
  | LAExpLitt  a   -> string_of_int a//int -> lAExp
  | LAExpVar   a   -> a//string -> lAExp
  | LAExpPlus  a b -> "("^lAExpToString a ^ "+" ^ lAExpToString b^")"//lAExp  -> lAExp -> lAExp
  | LAExpMinus a b -> "("^lAExpToString a ^ "-" ^ lAExpToString b^")"//lAExp  -> lAExp -> lAExp
  | LAExpMult  a b -> "("^lAExpToString a ^ "*" ^ lAExpToString b^")"//lAExp  -> lAExp -> lAExp
  | LAExpDiv   a b -> "("^lAExpToString a ^ "/" ^ lAExpToString b^")"//lAExp  -> lAExp -> lAExp

let rec lBExpToString x = match x with
  | LBExpLitt a   -> (if a then "true" else "false") //: bool -> lBExp
  | LBExpNot  a   -> "~"^lBExpToString a //: lBExp -> lBExp
  | LBExpAnd  a b -> "("^lBExpToString a ^ "&&" ^ lBExpToString b^")" //: lBExp -> lBExp -> lBExp
  | LBExpOr   a b -> "("^lBExpToString a ^ "||" ^ lBExpToString b^")" //: lBExp -> lBExp -> lBExp
  | LBExpEq   a b -> "("^lAExpToString a ^ "==" ^ lAExpToString b^")" //: lAExp -> lAExp -> lBExp
  | LBExpLe   a b -> "("^lAExpToString a ^ "<=" ^ lAExpToString b^")" //: lAExp -> lAExp -> lBExp

let rec lInstrAssignableToString x = match x with
  | AssignLAExp a -> lAExpToString a
  | AssignCall  fn args -> fn ^ "(" ^ String.concat ", " (L.map lAExpToString args) ^ ")"

let rec lFakeInstrToString x = match x with
  | LFakeInstrAssign a b -> a ^ " = " ^ lInstrAssignableToString b //: string -> lInstrAssignable -> lFakeInstr
  | LFakeInstrSkip       -> "SKIP"//: lFakeInstr
  | LFakeInstrSeq    a b -> lFakeInstrToString a^";"^lFakeInstrToString b//: lFakeInstr -> lFakeInstr -> lFakeInstr
  | LFakeInstrIf   c a b -> "if (" ^ lBExpToString c ^ ") { " ^ lFakeInstrToString a ^ " } else { " ^lFakeInstrToString b^" }" //: lBExp -> lFakeInstr -> lFakeInstr -> lFakeInstr
  | LFakeInstrWhile  c a -> "while (" ^ lBExpToString c ^ ") { " ^ lFakeInstrToString a ^" }"//: lBExp -> lFakeInstr -> lFakeInstr
  | LFakeInstrFunDef (FunFakeDef fn args _) -> "FunDef(TODO)"//: funFakeDef -> lFakeInstr

private
let uncurry f x = let (l,r) = x in f l r
private
let uncurry3 f x = let ((a,b),c) = x in f a b c

let op_apply = (fun (l, mb) -> match mb with
          | None -> l
          | Some (op, r) -> op l r
          )

let aexp_parser: parser lAExp =
  let rec no_rec (): parser lAExp =
          between_kwd "(" ")" (admitP (()<<()); delayMe h')
      <|> fp LAExpLitt number
      <|> fp LAExpVar word

  and h' (): parser lAExp = admitP (() << ()); let h = delayMe h' in
      op_apply @<< (
            no_rec ()
          <*> maybe ((
                (LAExpPlus *<< operator "+") <|> (LAExpMinus *<< operator "-")
            <|> (LAExpMult *<< operator "*") <|> (LAExpDiv *<< operator "/")
          ) <*> h)
        )
  in wrapspace (h' ())

let bexp_parser: parser lBExp =
  let rec no_rec (): parser lBExp = admitP (() << ()); let nr = delayMe no_rec in
          (LBExpNot @<< (operator "~" <*>> nr))
      <|> ptry (LBExpLitt true  *<< keyword "true" <|> LBExpLitt false *<< keyword "false")
      <|> ptry (between (operator "(") (operator ")") (delayMe h'))
      <|> ptry (fp (fun ((l, op), r) -> op l r)
        (aexp_parser <*> (
           (LBExpEq *<< operator "==") <|> (LBExpLe *<< operator "<=")
        ) <*> aexp_parser))
  and h' (): parser lBExp =   admitP (() << ()); let h = delayMe h' in
          op_apply @<<
          (no_rec () <*> maybe (
                ((LBExpAnd *<< operator "&&") <|> (LBExpOr *<< operator "||"))
            <*> h
          ))
  in wrapspace (h' ())

let rec lFakeInstrIsWF prog toplevel = match prog with
  | LFakeInstrSeq a b -> lFakeInstrIsWF a toplevel && lFakeInstrIsWF b toplevel
  | LFakeInstrIf  _ a b -> lFakeInstrIsWF a false && lFakeInstrIsWF b false
  | LFakeInstrWhile _ a -> lFakeInstrIsWF a false
  | LFakeInstrFunDef (FunFakeDef _ _ a) -> if toplevel then lFakeInstrIsWF a false else false
  | _ -> true

type lFakeInstrWF = r:lFakeInstr {lFakeInstrIsWF r true}

//let hAssignCall (var fName args =
//let hAssignExp (var, exp) = LFakeInstrAssign var (AssignLAExp exp)

let hAssign (var, eith) = match eith with
    | Inl (fName, args) -> LFakeInstrAssign var (AssignCall fName args)
    | Inr exp -> LFakeInstrAssign var (AssignLAExp exp)

let match_comment: parser string = spaces <*>> operator "//" <*>> string_satisfy (fun x -> x <> '\n')
let match_comments: parser (list string) = fp (fun x -> match x with | Some x -> x | None -> []) (maybe (many match_comment))

let hIf ((cond, body0), body1) = LFakeInstrIf cond body0 body1
let hWhile (cond, body) = LFakeInstrWhile cond body
let hFunction ((str,args),body) = LFakeInstrFunDef (FunFakeDef str args body)



let lFakeInstr_parser: parser (r:lFakeInstr {lFakeInstrIsWF r true}) =
   let z #a (arg:parser a) = arg  in
   let rec no_rec (tl:bool): parser (r:lFakeInstr {lFakeInstrIsWF r tl}) =
       admitP (() << ()); let nr = delayMe (h' false) in
   z (
       ( hIf @<<
         (((keyword "if" <*> operator "(") <*>> bexp_parser <<*> (operator ")" <*> operator "{")) <*>
           (nr <<*> (operator "}" <*> keyword "else" <*> operator "{")) <*>
           (nr <<*> operator "}"))
       )
   <|> ( hWhile @<< (
                ((keyword "while" <*> operator "(") <*>> bexp_parser <<*> (operator ")" <*> operator "{"))
            <*> (nr <<*> operator "}")
            )
       )
   <|> ( hFunction @<< (
                   (operator "function" <*>> word)
               <*> (match_list "(" ")" (operator ",") word <<*> operator "{")
               <*> (nr <<*> operator "}")
               )
       )
   <|> (LFakeInstrSkip *<< operator "SKIP")
   <|> (hAssign @<< (word <<*> operator "=" <*> (
             ptry (word <*> match_list "(" ")" (operator ",") aexp_parser)
         </> aexp_parser
       )))
   )
   and h' (tl:bool) (): parser (r:lFakeInstr {lFakeInstrIsWF r tl}) = admitP (() << ()); let h = delayMe (h' tl) in z (
       (fun (s1, s2) -> match s2 with
                     | None    -> s1
                     | Some s2 -> LFakeInstrSeq s1 s2
       ) @<< (no_rec tl <*> maybe (operator ";" <*>> h))//(match_comments <*>> h)))
     )
   in wrapspace (h' true ())
