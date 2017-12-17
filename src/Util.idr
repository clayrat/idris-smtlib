module Util

%default total
%access public export

infixr 1 =<<
infixr 1 <=<, >=>

-- | Left-to-right Kleisli composition of monads.
(>=>) : Monad m => (a -> m b) -> (b -> m c) -> (a -> m c)
(>=>) f g = \x => f x >>= g

-- | Right-to-left Kleisli composition of monads. `>=>` with the arguments flipped.
(<=<) : Monad m => (b -> m c) -> (a -> m b) -> (a -> m c)
(<=<) g f = \x => f x >>= g

(=<<) : Monad m => (a -> m b) -> m a -> m b
(=<<) f x = x >>= f