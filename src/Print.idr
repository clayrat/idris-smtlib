module Print

import Text.PrettyPrint.WL

import AST 

%default total
%access public export

ppSList : (a -> Doc) -> List a -> Doc
ppSList pp xs = parens (hsep (map pp xs))

ppListOpt : (a -> Doc) -> List a -> Doc
ppListOpt _  [] = empty
ppListOpt pp xs = space |+| hsep (map pp xs)

ppMaybe : (a -> Doc) -> Maybe a -> Doc
ppMaybe pp ma = maybe empty (\a => space |+| pp a) ma

ppSym : Symbol -> Doc
ppSym (MkSymbol s) = text s

ppLiteral : Literal -> Doc
ppLiteral (Numeral i) = integer i
ppLiteral (Decimal d) = double d

-- TODO use sizeAccessible? it doesn't like ppSort passed to map recursively
mutual 
  ppSort : Sort -> Doc
  ppSort (MkSort (MkIdentifier id _) []) = ppSym id
  ppSort (MkSort (MkIdentifier id _) subs@(_ :: _)) = parens (ppSym id |++| hsep (ppSortAux subs))

  ppSortAux : List Sort -> List Doc
  ppSortAux [] = []
  ppSortAux (s :: xs) = ppSort s :: ppSortAux xs

ppSortedVar : SortedVar -> Doc
ppSortedVar (MkSortedVar name sort) = ppSym name |++| ppSort sort

-- TODO HOFs again
mutual 
  ppSExpr : SExpr -> Doc
  ppSExpr (SList sexprs) = parens (hsep (ppSExprAux sexprs))
  ppSExpr (SKeyword kw) = text kw
  ppSExpr (SSymbol sym) = ppSym sym

  ppSExprAux : List SExpr -> List Doc
  ppSExprAux [] = []
  ppSExprAux (s :: sexps) = ppSExpr s :: ppSExprAux sexps

ppQId : QIdentifier -> Doc
ppQId (MkQIdentifier (MkIdentifier id _) Nothing)     = ppSym id
ppQId (MkQIdentifier (MkIdentifier id _) (Just sort)) = parens (text "as" |++| ppSym id |++| ppSort sort)

-- TODO HOFs yet again
mutual   
  ppVarBind : VarBinding -> Doc
  ppVarBind (MkVarBinding name term) = parens (ppSym name |++| ppTerm term)

  ppTerm : Term -> Doc
  ppTerm (Lit lit) = ppLiteral lit
  ppTerm (QI qid) = ppQId qid
  ppTerm (FunApp qid []) = ppQId qid
  ppTerm (FunApp qid ts) = parens (ppQId qid |++| hsep (ppTermAux ts))
  ppTerm (Let vb vbs t) = parens (text "let" |++| parens (ppVarBind vb |+| ppListOpt ppVarBind vbs) |++| ppTerm t)
  ppTerm (Forall sv svs t) = parens (text "forall" |++| parens (ppSortedVar sv |+| ppListOpt ppSortedVar svs) |++| ppTerm t) 
  ppTerm (Exists sv svs t) = parens (text "exists" |++| parens (ppSortedVar sv |+| ppListOpt ppSortedVar svs) |++| ppTerm t)

  ppTermAux : List Term -> List Doc
  ppTermAux [] = []
  ppTermAux (t :: ts) = ppTerm t :: ppTermAux ts
  
ppFunDef : FunDef -> Doc
ppFunDef (MkFunDef name svars ret body) = ppSym name |++| ppSList ppSortedVar svars |++| ppSort ret |++| ppTerm body

ppOption : SMTOption -> Doc
ppOption (ProduceModels b) = text ":produce-models" |++| bool b
ppOption (ProduceProofs b) = text ":produce-proofs" |++| bool b
ppOption (ProduceUnsatCores b) = text ":produce-unsat-cores" |++| bool b

ppCommand : Command -> Doc
ppCommand (Echo str)                = text "echo" |++| text str
ppCommand (DeclareConst name sort)  = text "declare-const" |++| ppSym name |++| ppSort sort
ppCommand (DeclareFun name ins out) = text "declare-fun" |++| ppSym name |++| ppSList ppSort ins |++| ppSort out
ppCommand (DeclareSort name arity)  = text "declare-sort" |++| ppSym name |+| ppMaybe int arity
ppCommand (DefineFun fundef)        = text "define-fun" |++| ppFunDef fundef
ppCommand (DefineSort name ps sort) = text "define-sort" |++| ppSym name |++| ppSList ppSym ps |++| ppSort sort
ppCommand (Assert term)             = text "assert" |++| ppTerm term
ppCommand CheckSat                  = text "check-sat"
ppCommand GetModel                  = text "get-model"
ppCommand (Push n)                  = text "push" |+| ppMaybe int n
ppCommand (Pop n)                   = text "pop" |+| ppMaybe int n
ppCommand (SetOption opt)           = text "set-option" |++| ppOption opt
ppCommand Reset                     = text "reset"

toDoc : Command -> Doc
toDoc c = parens $ ppCommand c

ppScript : List Command -> Doc
ppScript cs = vsep $ map toDoc cs
