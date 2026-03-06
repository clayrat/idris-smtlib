module SMTLib.AST

%default total

public export
data Symbol = MkSymbol String

public export
data Literal = Numeral Integer
             | Decimal Double -- TODO something with better precision
             | StringLit String

public export
data SExpr = SList (List SExpr)
           | SKeyword String
           | SSymbol Symbol
           | SLiteral Literal

-- Identifier used to be indexed with Index type, that could be either SSymbol or SNumeral.
-- This is actually the current (2.5) SMT-LIB standard.
-- But in order to support some extensions in Z3, we use full SExpr as index.
public export
data Identifier = MkIdentifier Symbol (List SExpr)
public export
data Sort = MkSort Identifier (List Sort)
public export
data QIdentifier = MkQIdentifier Identifier (Maybe Sort)
public export
data SortedVar = MkSortedVar Symbol Sort

mutual
  public export
  data VarBinding = MkVarBinding Symbol Term
  public export
  data Term = Lit Literal
            | QI QIdentifier
            | FunApp QIdentifier (List Term)
            | Let VarBinding (List VarBinding) Term   -- TODO NEList ?
            | Forall SortedVar (List SortedVar) Term  --
            | Exists SortedVar (List SortedVar) Term  --
            -- TODO rest

-- TODO inline to DefineFun ?
public export
data FunDef = MkFunDef Symbol (List SortedVar) Sort Term

public export
data SMTOption = ProduceModels Bool
               | ProduceProofs Bool
               | ProduceUnsatCores Bool
               -- TODO rest

public export
data Command = Echo String
             | DeclareConst Symbol Sort
             | DeclareFun Symbol (List Sort) Sort
             | DeclareSort Symbol (Maybe Int)
             | DefineFun FunDef
             | DefineSort Symbol (List Symbol) Sort
             | Assert Term
             | CheckSat
             | GetModel
             | Push (Maybe Int)
             | Pop (Maybe Int)
             | SetOption SMTOption
             | Reset

-------- 2.6
-- DeclareDatatype
-- DeclareDatatypes

-------- Z3-specific
-- Display
-- Simplify
-- Eval