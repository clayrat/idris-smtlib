module Util

%default total
%access public export

infixl 4 <**>    

(<**>) : Applicative f => f a -> f (a -> b) -> f b
(<**>) = flip (<*>)

data Const a b = MkConst a

getConst : Const a b -> a
getConst (MkConst a) = a

Functor (Const m) where
  map _ (MkConst v) = MkConst v

Monoid m => Applicative (Const m) where
  pure _ = MkConst neutral
  (MkConst a) <*> (MkConst b) = MkConst (a <+> b)