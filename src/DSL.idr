module DSL

import Control.Monad.Identity
import Control.Monad.Freer
import Control.Monad.Writer

import AST

%default total
%access public export
{-
declareInt : String -> Command
declareInt name = DeclareConst (MkSymbol name) (MkSort (MkIdentifier (MkSymbol "Int") []) [])

declareReal : String -> Command
declareReal name = DeclareConst (MkSymbol name) (MkSort (MkIdentifier (MkSymbol "Real") []) [])

num : Integer -> Term
num n = Lit (Numeral n)

dec : Double -> Term
dec d = Lit (Decimal d)

var : String -> Term
var name = QI (MkQIdentifier (MkIdentifier (MkSymbol name) []) Nothing)


-}

{-
data SMTInt = MkSMTInt Term

Num SMTInt where
  fromInteger i = MkSMTInt $ Lit (Numeral i)
  (MkSMTInt t1) + (MkSMTInt t2) = MkSMTInt $ FunApp (MkQIdentifier (MkIdentifier (MkSymbol "+") []) Nothing) [ t1, t2 ]
  (MkSMTInt t1) * (MkSMTInt t2) = MkSMTInt $ FunApp (MkQIdentifier (MkIdentifier (MkSymbol "*") []) Nothing) [ t1, t2 ]

data SMTReal = MkSMTReal Term

d : Double -> SMTReal
d x = MkSMTReal $ Lit (Decimal x)

Num SMTReal where
  fromInteger i = MkSMTReal $ Lit (Decimal $ cast i)
  (MkSMTReal t1) + (MkSMTReal t2) = MkSMTReal $ FunApp (MkQIdentifier (MkIdentifier (MkSymbol "+") []) Nothing) [ t1, t2 ]
  (MkSMTReal t1) * (MkSMTReal t2) = MkSMTReal $ FunApp (MkQIdentifier (MkIdentifier (MkSymbol "*") []) Nothing) [ t1, t2 ]
-}

declare : String -> String -> Command
declare name sort = DeclareConst (MkSymbol name) (MkSort (MkIdentifier (MkSymbol sort) []) [])

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
  t1 + t2 = app "+" [ t1, t2 ]
  t1 * t2 = app "*" [ t1, t2 ]

Neg Term where
  negate t = app "-" [ 0, t ]  
  t1 - t2 = app "-" [ t1, t2 ]  
  
d : Double -> Term
d x = Lit (Decimal x)


data SMTReal = RealVar String

toTerm : SMTReal -> Term
toTerm (RealVar name) = var name

data SMTInt = IntVar String

toTermI : SMTInt -> Term
toTermI (IntVar name) = var name

data SMTCommandF : Type -> Type where
  SDeclareReal : String -> SMTCommandF SMTReal  
  SDeclareInt : String -> SMTCommandF SMTInt
  SAssert : Term -> SMTCommandF ()
  SCheckSat : SMTCommandF ()
  SGetModel : SMTCommandF ()

SMTCommand : Type -> Type
SMTCommand = Freer SMTCommandF

declareReal : String -> SMTCommand SMTReal  
declareReal s = SDeclareReal s `Then` Return 

declareInt : String -> SMTCommand SMTInt
declareInt s = SDeclareInt s `Then` Return 

assert : Term -> SMTCommand ()
assert t = SAssert t `Then` Return

checkSat : SMTCommand ()
checkSat = SCheckSat `Then` Return 

getModel : SMTCommand ()
getModel = SGetModel `Then` Return

writeCommands : SMTCommand a -> Writer (List Command) a
writeCommands = foldFreer $ \instruction => 
  case instruction of
    SDeclareReal s => do tell [declare s "Real"] 
                         pure $ RealVar s
    SDeclareInt s => do tell [declare s "Int"] 
                        pure $ IntVar s
    SAssert t => tell [Assert t]
    SCheckSat => tell [CheckSat]
    SGetModel => tell [GetModel]

renderCommands : SMTCommand a -> List Command
renderCommands = snd . runIdentity . runWriterT . writeCommands  