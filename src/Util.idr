module Util

%default total
%access public export

infixr 1 =<<, <=<, >=>

infixl 4 <**>    

||| Left-to-right Kleisli composition of monads.
(>=>) : Monad m => (a -> m b) -> (b -> m c) -> (a -> m c)
(>=>) f g = \x => f x >>= g

||| Right-to-left Kleisli composition of monads, flipped version of `>=>`.
(<=<) : Monad m => (b -> m c) -> (a -> m b) -> (a -> m c)
(<=<) = flip (>=>)

||| Right-to-left monadic bind, flipped version of `>>=`.
(=<<) : Monad m => (a -> m b) -> m a -> m b
(=<<) = flip (>>=)

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