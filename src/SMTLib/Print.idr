module SMTLib.Print

import Text.PrettyPrint.Prettyprinter

import SMTLib.AST

%default total

public export
ppSList : (a -> Doc ()) -> List a -> Doc ()
ppSList pp xs = parens (hsep (map pp xs))

public export
ppListOpt : (a -> Doc ()) -> List a -> Doc ()
ppListOpt _  [] = neutral
ppListOpt pp xs = space <++> hsep (map pp xs)

public export
ppMaybe : (a -> Doc ()) -> Maybe a -> Doc ()
ppMaybe pp ma = maybe neutral (\a => space <++> pp a) ma

public export
ppSym : Symbol -> Doc ()
ppSym (MkSymbol s) = pretty s

public export
ppLiteral : Literal -> Doc ()
ppLiteral (Numeral i) = pretty i
ppLiteral (Decimal d) = pretty d
ppLiteral (StringLit s) = pretty "\"" <+> pretty s <+> pretty "\""

-- TODO use sizeAccessible? it doesn't like ppSort passed to map recursively
mutual
  public export
  ppSort : Sort -> Doc ()
  ppSort (MkSort (MkIdentifier id _) []) = ppSym id
  ppSort (MkSort (MkIdentifier id _) subs@(_ :: _)) = parens (ppSym id <++> hsep (ppSortAux subs))

  public export
  ppSortAux : List Sort -> List (Doc ())
  ppSortAux [] = []
  ppSortAux (s :: xs) = ppSort s :: ppSortAux xs

public export
ppSortedVar : SortedVar -> Doc ()
ppSortedVar (MkSortedVar name sort) = ppSym name <++> ppSort sort

-- TODO HOFs again
mutual
  public export
  ppSExpr : SExpr -> Doc ()
  ppSExpr (SList sexprs) = parens (hsep (ppSExprAux sexprs))
  ppSExpr (SKeyword kw) = pretty kw
  ppSExpr (SSymbol sym) = ppSym sym
  ppSExpr (SLiteral lit) = ppLiteral lit

  public export
  ppSExprAux : List SExpr -> List (Doc ())
  ppSExprAux [] = []
  ppSExprAux (s :: sexps) = ppSExpr s :: ppSExprAux sexps

public export
ppQId : QIdentifier -> Doc ()
ppQId (MkQIdentifier (MkIdentifier id _) Nothing)     = ppSym id
ppQId (MkQIdentifier (MkIdentifier id _) (Just sort)) = parens (pretty "as" <++> ppSym id <++> ppSort sort)

-- TODO HOFs yet again
mutual
  public export
  ppVarBind : VarBinding -> Doc ()
  ppVarBind (MkVarBinding name term) = parens (ppSym name <++> (assert_total $ ppTerm term))

  public export
  ppTerm : Term -> Doc ()
  ppTerm (Lit lit) = ppLiteral lit
  ppTerm (QI qid) = ppQId qid
  ppTerm (FunApp qid []) = ppQId qid
  ppTerm (FunApp qid ts) = parens (ppQId qid <++> hsep (ppTermAux ts))
  ppTerm (Let vb vbs t) = parens (pretty "let" <++> parens (ppVarBind vb <+> ppListOpt ppVarBind vbs) <++> ppTerm t)
  ppTerm (Forall sv svs t) = parens (pretty "forall" <++> parens (ppSortedVar sv <+> ppListOpt ppSortedVar svs) <++> ppTerm t)
  ppTerm (Exists sv svs t) = parens (pretty "exists" <++> parens (ppSortedVar sv <+> ppListOpt ppSortedVar svs) <++> ppTerm t)

  public export
  ppTermAux : List Term -> List (Doc ())
  ppTermAux [] = []
  ppTermAux (t :: ts) = ppTerm t :: ppTermAux ts

public export
ppFunDef : FunDef -> Doc ()
ppFunDef (MkFunDef name svars ret body) = ppSym name <++> ppSList ppSortedVar svars <++> ppSort ret <++> ppTerm body

||| Convert Bool to SMT-LIB format (lowercase true/false)
ppBool : Bool -> Doc ()
ppBool True = pretty "true"
ppBool False = pretty "false"

public export
ppOption : SMTOption -> Doc ()
ppOption (ProduceModels b) = pretty ":produce-models" <++> ppBool b
ppOption (ProduceProofs b) = pretty ":produce-proofs" <++> ppBool b
ppOption (ProduceUnsatCores b) = pretty ":produce-unsat-cores" <++> ppBool b

public export
ppCommand : Command -> Doc ()
ppCommand (Echo str)                = pretty "echo" <++> pretty str
ppCommand (DeclareConst name sort)  = pretty "declare-const" <++> ppSym name <++> ppSort sort
ppCommand (DeclareFun name ins out) = pretty "declare-fun" <++> ppSym name <++> ppSList ppSort ins <++> ppSort out
ppCommand (DeclareSort name arity)  = pretty "declare-sort" <++> ppSym name <+> ppMaybe (pretty . cast {to=Integer}) arity
ppCommand (DefineFun fundef)        = pretty "define-fun" <++> ppFunDef fundef
ppCommand (DefineSort name ps sort) = pretty "define-sort" <++> ppSym name <++> ppSList ppSym ps <++> ppSort sort
ppCommand (Assert term)             = pretty "assert" <++> ppTerm term
ppCommand CheckSat                  = pretty "check-sat"
ppCommand GetModel                  = pretty "get-model"
ppCommand (Push n)                  = pretty "push" <+> ppMaybe (pretty . cast {to=Integer}) n
ppCommand (Pop n)                   = pretty "pop" <+> ppMaybe (pretty . cast {to=Integer}) n
ppCommand (SetOption opt)           = pretty "set-option" <++> ppOption opt
ppCommand Reset                     = pretty "reset"

public export
toDoc : Command -> Doc ()
toDoc c = parens $ ppCommand c

public export
ppScript : List Command -> Doc ()
ppScript cs = vsep $ map toDoc cs
