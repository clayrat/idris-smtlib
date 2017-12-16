module AST

%default total
%access public export

data Symbol = MkSymbol String

data SExpr = SList (List SExpr)
           | SKeyword String
           | SSymbol Symbol

data Literal = Numeral Integer
             | Decimal Double -- TODO something with better precision

-- Identifier used to be indexed with Index type, that could be either SSymbol or SNumeral.
-- This is actually the current (2.5) SMT-LIB standard.
-- But in order to support some extensions in Z3, we use full SExpr as index.
data Identifier = MkIdentifier Symbol (List SExpr)
data Sort = MkSort Identifier (List Sort)
data QIdentifier = MkQIdentifier Identifier (Maybe Sort)
data SortedVar = MkSortedVar Symbol Sort

mutual
  data VarBinding = MkVarBinding Symbol Term
  data Term = Lit Literal
            | QI QIdentifier
            | FunApp QIdentifier (List Term)
            | Let VarBinding (List VarBinding) Term   -- TODO NEList ?
            | Forall SortedVar (List SortedVar) Term  --
            | Exists SortedVar (List SortedVar) Term  --
            -- TODO rest

-- TODO inline to DefineFun ?
data FunDef = MkFunDef Symbol (List SortedVar) Sort Term

data SMTOption = ProduceModels Bool
               | ProduceProofs Bool
               | ProduceUnsatCores Bool
               -- TODO rest

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