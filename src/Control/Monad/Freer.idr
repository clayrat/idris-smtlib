module Control.Monad.Freer

import Util
--import Control.Monad ((<=<))
import Control.Monad.Free

import Data.Bifunctor
--import Data.Functor.Classes
--import Data.Functor.Foldable

%default total
%access public export

data Freer : (f : Type -> Type) -> (a : Type) -> Type where
  Return : a -> Freer f a
  Then : f x -> (x -> Freer f a) -> Freer f a

Functor (Freer f) where
  map f = go
    where go (Return result) = Return (f result)
          go (Then step yield) = assert_total $ Then step (go . yield)

Applicative (Freer f) where
  pure = Return

  (Return f) <*> param = map f param
  (Then action yield) <*> param = assert_total $ Then action ((<*> param) . yield)

Monad (Freer f) where
  (Return a) >>= f = f a
  (Then r f) >>= g = assert_total $ Then r (g <=< f)

liftF : f a -> Freer f a
liftF action = action `Then` Return

hoistFreer : {f, g : Type -> Type} -> ({a : Type} -> f a -> g a) -> Freer f b -> Freer g b
hoistFreer fg {b} = go
  where 
    go : Freer f b -> Freer g b
    go (Return result) = Return result
    go (Then step yield) = assert_total $ Then (fg step) (go . yield)

-- | Tear down a 'Freer' 'Monad' using iteration with an explicit continuation.
--
--   This is analogous to 'iter' with a continuation for the interior values, and is therefore suitable for defining interpreters for GADTs/types lacking a 'Functor' instance.
iterFreer : ({x : Type} -> (x -> a) -> f x -> a) -> Freer f a -> a
iterFreer algebra = go
  where go (Return result) = result
        go (Then action continue) = assert_total $ algebra (go . continue) action

-- | Tear down a 'Freer' 'Monad' using iteration.
--
--   This is analogous to 'cata' where the 'Return'ed values are placeholders for the result of the computation.
iter : Functor f => (f a -> a) -> Freer f a -> a
iter algebra = iterFreer (\yield => algebra . map yield)

-- | Tear down a 'Freer' 'Monad' using iteration with an explicit continuation in some 'Applicative' context.
--
--   This is analogous to 'iterA' with a continuation for the interior values, and is therefore suitable for defining interpreters for GADTs/types lacking a 'Functor' instance.
iterFreerA : Applicative m => ({x : Type} -> (x -> m a) -> f x -> m a) -> Freer f a -> m a
iterFreerA algebra r = iterFreer algebra (map pure r)

-- | Tear down a 'Freer' 'Monad' using iteration in some 'Applicative' context.
--
--   This is analogous to 'cata' where the 'Return'ed values are placeholders for the result of the computation.
iterA : (Functor f, Applicative m) => (f (m a) -> m a) -> Freer f a -> m a
iterA algebra = iterFreerA (\yield => algebra . map yield)

-- | Run a program to completion by repeated refinement, and return its result.
runFreer : ({x : Type} -> f x -> Freer f x) -> Freer f result -> result
runFreer refine = go
  where go : Freer f z -> z
        go = assert_total $ iterFreer (\xz, fx => xz $ go $ refine fx)

-- | Run a program to completion by repeated refinement in some `Monad`ic context, and return its result.
runFreerM : Monad m => ({x : Type} -> f x -> Freer f (m x)) -> Freer f result -> m result
runFreerM {m} refine r = go (map pure r)
  where go : Freer f (m x) -> m x
        go = assert_total $ iterFreer ((. (go . refine)) . (=<<))

-- | Run a single step of a program by refinement, returning `Either` its result or the next step.
stepFreer : ({x : Type} -> f x -> Freer f x) -> Freer f result -> Either result (Freer f result)
stepFreer refine = go
  where go (Return a) = Left a
        go (Then step yield) = Right (refine step >>= yield)

-- | Run a program to completion by repeated refinement, returning the list of steps up to and including the final result.
--
--   The steps are unfolded lazily, making this suitable for stepwise evaluation of nonterminating programs.
freerSteps : ({x : Type} -> f x -> Freer f x) -> Freer f result -> List (Freer f result)
freerSteps refine = go
  where go r = case stepFreer refine r of
          Left a => [Return a]
          Right step => assert_total $ step :: go step

retract : Monad m => Freer m a -> m a
retract = iterFreerA (=<<)

foldFreer : Monad m => ({x : Type} -> f x -> m x) -> Freer f a -> m a
foldFreer f = retract . hoistFreer f

cutoff : Nat -> Freer f a -> Freer f (Either (Freer f a) a)
cutoff Z r = pure (Left r)
cutoff (S n) (Then step yield) = Then step (cutoff n . yield)
cutoff _ r = Right <$> r

MonadFree (Freer f) f where
  wrap action = action `Then` id


(Foldable f) => Foldable (Freer f) where
  foldr ff c (Return a) = ff a c
  foldr ff c (Then r t) = foldr (\x,c1 => foldr ff c1 (t x)) c r
    
(Traversable f) => Traversable (Freer f) where
  traverse f (Return a) = pure <$> f a
  traverse f (Then r t) = wrap <$> traverse (\a => traverse f (t a)) r   
{-
instance Show1 f => Show1 (Freer f) where
  liftShowsPrec sp sl = go
    where go d (Return a) = showsUnaryWith sp "Return" d a
          go d (Then step yield) = showsBinaryWith (liftShowsPrec ((. yield) . go) (liftShowList sp sl . fmap yield)) (const showString) "Then" d step "_"

instance (Show1 f, Show a) => Show (Freer f a) where
  showsPrec = liftShowsPrec showsPrec showList

instance Eq1 f => Eq1 (Freer f) where
  liftEq eqResult = go
    where go (Return result1) (Return result2) = eqResult result1 result2
          go (Then step1 yield1) (Then step2 yield2) = liftEq (\ x1 x2 -> go (yield1 x1) (yield2 x2)) step1 step2
          go _ _ = False

instance (Eq1 f, Eq a) => Eq (Freer f a) where
  (==) = liftEq (==)
-}

data FreerF : (f : Type -> Type) -> (a : Type) -> (b : Type) -> Type where
  ReturnF : a -> FreerF f a b
  ThenF : f x -> (x -> b) -> FreerF f a b

liftFreerF : f b -> FreerF f a b
liftFreerF action = action `ThenF` id

hoistFreerF : ({a : Type} -> f a -> g a) -> FreerF f b c -> FreerF g b c
hoistFreerF _  (ReturnF result) = ReturnF result
hoistFreerF fg (ThenF step yield) = ThenF (fg step) yield

Functor (FreerF f a) where
  map _ (ReturnF a) = ReturnF a
  map f (ThenF r g) = ThenF r (f . g)

Bifunctor (FreerF f) where
  bimap f _ (ReturnF result) = ReturnF (f result)
  bimap _ g (ThenF step yield) = ThenF step (g . yield)

  {-
Foldable f => Foldable (FreerF f a) where
  foldr ff c (ReturnF _) = ?wat
  --  foldMap _ (ReturnF _) = mempty
--  foldMap f (ThenF step yield) = foldMap (f . yield) step

Traversable f => Traversable (FreerF f a) where
  traverse _ (ReturnF result) = pure (ReturnF result)
  traverse f (ThenF step yield) = liftFreerF <$> traverse (f . yield) step

instance Eq1 f => Eq2 (FreerF f) where
  liftEq2 eqResult eqRecur (ReturnF result1) (ReturnF result2) = eqResult result1 result2
  liftEq2 _ eqRecur (ThenF step1 yield1) (ThenF step2 yield2) = liftEq (\ x1 x2 -> eqRecur (yield1 x1) (yield2 x2)) step1 step2
  liftEq2 _ _ _ _ = False

instance (Eq1 f, Eq a) => Eq1 (FreerF f a) where
  liftEq = liftEq2 (==)

instance (Eq1 f, Eq a, Eq b) => Eq (FreerF f a b) where
  (==) = liftEq (==)


instance Show1 f => Show2 (FreerF f) where
  liftShowsPrec2 sp1 _ _ _ d (ReturnF result) = showsUnaryWith sp1 "ReturnF" d result
  liftShowsPrec2 sp1 _ sp2 sa2 d (ThenF step yield) = showsBinaryWith (liftShowsPrec ((. yield) . sp2) (sa2 . fmap yield)) (const showString) "ThenF" d step "_"

instance (Show1 f, Show a) => Show1 (FreerF f a) where
  liftShowsPrec = liftShowsPrec2 showsPrec showList

instance (Show1 f, Show a, Show b) => Show (FreerF f a b) where
  showsPrec = liftShowsPrec showsPrec showList


type instance Base (Freer f a) = FreerF f a

instance Recursive (Freer f a) where
  project (Return a) = ReturnF a
  project (Then r t) = ThenF r t
  -- INLINE project --

instance Corecursive (Freer f a) where
  embed (ReturnF a) = Return a
  embed (ThenF r t) = Then r t
  -- INLINE embed --
--
-- INLINE hoistFreer 
-}