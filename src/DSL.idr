module DSL

import AST

%default total
%access public export

declareReal : String -> Command
declareReal name = DeclareConst (MkSymbol name) (MkSort (MkIdentifier (MkSymbol "Real") []) [])

num : Integer -> Term
num n = Lit (Numeral n)

dec : Double -> Term
dec d = Lit (Decimal d)

var : String -> Term
var name = QI (MkQIdentifier (MkIdentifier (MkSymbol name) []) Nothing)

app : String -> List Term -> Term
app nam ts = FunApp (MkQIdentifier (MkIdentifier (MkSymbol nam) []) Nothing) ts

assert : Term -> Command
assert = Assert

checkSat : Command
checkSat = CheckSat

getModel : Command
getModel = GetModel