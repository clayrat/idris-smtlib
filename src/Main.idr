module Main

%default total
%access public export

data Symbol = MkSymbol String

data SExpr = SList (List SExpr) | SKeyword String | SSymbol Symbol 

-- Identifier used to be indexed with Index type, that could be either SSymbol or SNumeral.
-- This is actually the current (2.5) SMT-LIB standard.                                    
-- But in order to support some extensions in Z3, we use full SExpr as index.              
data Identifier = MkIdentifier Symbol (List SExpr)

data Sort = MkSort Identifier (List Sort)

data SortedVar = MkSortedVar Symbol Sort

mutual 
  data VarBinding = MkVarBinding Symbol Term
  data Term = Expr SExpr
            | Let VarBinding (List VarBinding) Term
            | Forall SortedVar (List SortedVar) Term
            | Exists SortedVar (List SortedVar) Term
            -- TODO rest
            
data FunDef = MkFunDef Symbol (List SortedVar) Sort Term

data SMTOption = ProduceModels Bool 
               | ProduceProofs Bool 
               | ProduceUnsatCores Bool
               -- TODO rest

data Command = Echo String
             | DeclareConst Symbol Sort
             | DeclareFun Symbol (List Sort) Sort
             | DeclareSort Symbol Int
             | DefineFun FunDef
             | DefineSort Symbol (List Symbol) Sort
             | Assert Term
             | CheckSat
             | GetModel
             | Push Int
             | Pop Int
             | SetOption SMTOption
             | Reset

-------- 2.6
-- DeclareDatatype
-- DeclareDatatypes          

-------- Z3-specific
-- Display
-- Simplify   
-- Eval

main : IO ()
main = printLn "wop"
