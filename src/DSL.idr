module DSL

import Control.Monad.Identity
import Control.Monad.Freer
import Control.Monad.Writer

import AST

%default total
%access public export

declareConst : String -> String -> Command
declareConst name sort = DeclareConst (MkSymbol name) (MkSort (MkIdentifier (MkSymbol sort) []) [])

var : String -> Term
var name = QI (MkQIdentifier (MkIdentifier (MkSymbol name) []) Nothing)

app : String -> List Term -> Term
app nam ts = FunApp (MkQIdentifier (MkIdentifier (MkSymbol nam) []) Nothing) ts

-- TODO something more typesafe?
eq : Term -> Term -> Term
eq t1 t2 = app "=" [t1, t2]

le : Term -> Term -> Term
le t1 t2 = app "<=" [t1, t2]

and : Term -> Term -> Term
and t1 t2 = app "and" [t1, t2]

distinct : List Term -> Term
distinct = app "distinct"

Num Term where
  fromInteger i = Lit (Numeral i)
  t1 + t2 = app "+" [t1, t2]
  t1 * t2 = app "*" [t1, t2]

Neg Term where
  negate t = app "-" [0, t]
  t1 - t2 = app "-" [t1, t2]

index : Term -> Term -> Term
index t1 t2 = app "_" [t1, t2]

bvand : Term -> Term -> Term
bvand t1 t2 = app "bvand" [t1, t2]

bvashr : Term -> Term -> Term
bvashr t1 t2 = app "bvashr" [t1, t2]

--bvlit : String -> Nat -> Term
--bvlit s n = index 

d : Double -> Term
d x = Lit (Decimal x)

data SMTReal = RealVar String

toTerm : SMTReal -> Term
toTerm (RealVar name) = var name

data SMTInt = IntVar String

toTermI : SMTInt -> Term
toTermI (IntVar name) = var name

data SMTBV : Nat -> Type where 
  BVVar : String -> (n : Nat) -> SMTBV n

toTermBV : SMTBV n -> Term
toTermBV (BVVar name _) = var name

data SMTScriptF : Type -> Type where
  SDeclareReal : String -> SMTScriptF SMTReal
  SDeclareInt : String -> SMTScriptF SMTInt
  SDeclareBV : String -> (n : Nat) -> SMTScriptF (SMTBV n)
  SAssert : Term -> SMTScriptF ()
  SCheckSat : SMTScriptF ()
  SGetModel : SMTScriptF ()

SMTScript : Type -> Type
SMTScript = Freer SMTScriptF

declareReal : String -> SMTScript SMTReal
declareReal s = liftF $ SDeclareReal s

declareInt : String -> SMTScript SMTInt
declareInt s = liftF $ SDeclareInt s

declareBV : String -> (n : Nat) -> SMTScript (SMTBV n)
declareBV s n = liftF $ SDeclareBV s n

assert : Term -> SMTScript ()
assert t = liftF $ SAssert t 

checkSat : SMTScript ()
checkSat = liftF SCheckSat 

getModel : SMTScript ()
getModel = liftF SGetModel

writeCommands : SMTScript a -> Writer (List Command) a
writeCommands = foldFreer $ \instruction =>
  case instruction of
    SDeclareReal s => do tell [declareConst s "Real"]
                         pure $ RealVar s
    SDeclareInt s => do tell [declareConst s "Int"]
                        pure $ IntVar s
    SDeclareBV s n => do tell [declareConst s $ "(_ BitVec " ++ show n ++ ")"]
                         pure $ BVVar s n
    SAssert t => tell [Assert t]
    SCheckSat => tell [CheckSat]
    SGetModel => tell [GetModel]

renderCommands : SMTScript a -> List Command
renderCommands = snd . runIdentity . runWriterT . writeCommands