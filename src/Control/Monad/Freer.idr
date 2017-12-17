module Control.Monad.Freer

import Util
import Control.Monad.Free
import Data.Bifunctor

%default total
%access public export

data Freer : (f : Type -> Type) -> (a : Type) -> Type where
  Pure : a -> Freer f a
  Bind : f x -> (x -> Freer f a) -> Freer f a

Functor (Freer f) where
  map f (Pure result) = Pure (f result)
  map f (Bind step yield) = assert_total $ Bind step (map f . yield)

Applicative (Freer f) where
  pure = Pure

  (Pure f) <*> param = map f param
  (Bind action yield) <*> param = assert_total $ Bind action ((<*> param) . yield)

Monad (Freer f) where
  (Pure a) >>= f = f a
  (Bind r f) >>= g = assert_total $ Bind r (g <=< f)

liftF : f a -> Freer f a
liftF action = action `Bind` Pure

hoistFreer : {f, g : Type -> Type} -> ({a : Type} -> f a -> g a) -> Freer f b -> Freer g b
hoistFreer _  (Pure result)   = Pure result
hoistFreer fg (Bind step yield) = assert_total $ Bind (fg step) (hoistFreer fg . yield)

-- | Tear down a 'Freer' 'Monad' using iteration with an explicit continuation.
--
-- This is analogous to 'iter' with a continuation for the interior values, and
-- is therefore suitable for defining interpreters for GADTs/types lacking a
-- `Functor` instance.
iterFreer : ({x : Type} -> (x -> a) -> f x -> a) -> Freer f a -> a
iterFreer _       (Pure result)        = result
iterFreer algebra (Bind action continue) = assert_total $ algebra (iterFreer algebra . continue) action

-- | Tear down a 'Freer' 'Monad' using iteration.
--
-- This is analogous to 'cata' where the 'Pure'ed values are placeholders for
-- the result of the computation.
iter : Functor f => (f a -> a) -> Freer f a -> a
iter algebra = iterFreer (\yield => algebra . map yield)

-- | Tear down a 'Freer' 'Monad' using iteration with an explicit continuation in some 'Applicative' context.
--
-- This is analogous to 'iterA' with a continuation for the interior values, and
-- is therefore suitable for defining interpreters for GADTs/types lacking a
-- 'Functor' instance.
iterFreerA : Applicative m => ({x : Type} -> (x -> m a) -> f x -> m a) -> Freer f a -> m a
iterFreerA algebra r = iterFreer algebra (map pure r)

-- | Tear down a 'Freer' 'Monad' using iteration in some 'Applicative' context.
--
--   This is analogous to 'cata' where the 'Pure' values are placeholders for
-- the result of the computation.
iterA : (Functor f, Applicative m) => (f (m a) -> m a) -> Freer f a -> m a
iterA algebra = iterFreerA (\yield => algebra . map yield)

-- | Run a program to completion by repeated refinement, and return its result.
runFreer : ({x : Type} -> f x -> Freer f x) -> Freer f result -> result
runFreer refine = assert_total $ iterFreer (\xz, fx => xz $ runFreer refine $ refine fx)

-- | Run a program to completion by repeated refinement in some `Monad`ic
-- | context, and return its result.
runFreerM : Monad m => ({x : Type} -> f x -> Freer f (m x)) -> Freer f result -> m result
runFreerM {m} refine r = go (map pure r)
  where go : Freer f (m x) -> m x
        go = assert_total $ iterFreer ((. (go . refine)) . (=<<))

-- | Run a single step of a program by refinement, returning `Either` its result
-- | or the next step.
stepFreer : ({x : Type} -> f x -> Freer f x) -> Freer f result -> Either result (Freer f result)
stepFreer _      (Pure a)        = Left a
stepFreer refine (Bind step yield) = Right (refine step >>= yield)

-- | Run a program to completion by repeated refinement, returning the list of
-- | steps up to and including the final result. 
-- 
--  The steps are unfolded lazily, making this suitable for stepwise evaluation
-- of nonterminating programs.
freerSteps : ({x : Type} -> f x -> Freer f x) -> Freer f result -> List (Freer f result)
freerSteps refine r = case stepFreer refine r of
  Left a => [Pure a]
  Right step => assert_total $ step :: freerSteps refine step

retract : Monad m => Freer m a -> m a
retract = iterFreerA (=<<)

foldFreer : Monad m => ({x : Type} -> f x -> m x) -> Freer f a -> m a
foldFreer f = retract . hoistFreer f

cutoff : Nat -> Freer f a -> Freer f (Either (Freer f a) a)
cutoff Z r = pure (Left r)
cutoff (S n) (Bind step yield) = Bind step (cutoff n . yield)
cutoff _ r = Right <$> r

MonadFree (Freer f) f where
  wrap action = action `Bind` id

(Foldable f) => Foldable (Freer f) where
  foldr ff c (Pure a) = ff a c
  foldr ff c (Bind r t) = foldr (\x,c1 => foldr ff c1 (t x)) c r
    
(Traversable f) => Traversable (Freer f) where
  traverse f (Pure a) = pure <$> f a
  traverse f (Bind r t) = wrap <$> traverse (\a => traverse f (t a)) r   
{-
instance Show1 f => Show1 (Freer f) where
  liftShowsPrec sp sl = go
    where go d (Pure a) = showsUnaryWith sp "Pure" d a
          go d (Bind step yield) = showsBinaryWith (liftShowsPrec ((. yield) . go) (liftShowList sp sl . fmap yield)) (const showString) "Bind" d step "_"

instance (Show1 f, Show a) => Show (Freer f a) where
  showsPrec = liftShowsPrec showsPrec showList

instance Eq1 f => Eq1 (Freer f) where
  liftEq eqResult = go
    where go (Pure result1) (Pure result2) = eqResult result1 result2
          go (Bind step1 yield1) (Bind step2 yield2) = liftEq (\ x1 x2 -> go (yield1 x1) (yield2 x2)) step1 step2
          go _ _ = False

instance (Eq1 f, Eq a) => Eq (Freer f a) where
  (==) = liftEq (==)
-}

data FreerF : (f : Type -> Type) -> (a : Type) -> (b : Type) -> Type where
  PureF : a -> FreerF f a b
  BindF : f x -> (x -> b) -> FreerF f a b

liftFreerF : f b -> FreerF f a b
liftFreerF action = action `BindF` id

hoistFreerF : ({a : Type} -> f a -> g a) -> FreerF f b c -> FreerF g b c
hoistFreerF _  (PureF result) = PureF result
hoistFreerF fg (BindF step yield) = BindF (fg step) yield

Functor (FreerF f a) where
  map _ (PureF a) = PureF a
  map f (BindF r g) = BindF r (f . g)

Bifunctor (FreerF f) where
  bimap f _ (PureF result) = PureF (f result)
  bimap _ g (BindF step yield) = BindF step (g . yield)

  {-
Foldable f => Foldable (FreerF f a) where
  foldr ff c (PureF _) = ?wat
  --  foldMap _ (PureF _) = mempty
--  foldMap f (BindF step yield) = foldMap (f . yield) step

Traversable f => Traversable (FreerF f a) where
  traverse _ (PureF result) = pure (PureF result)
  traverse f (BindF step yield) = liftFreerF <$> traverse (f . yield) step

instance Eq1 f => Eq2 (FreerF f) where
  liftEq2 eqResult eqRecur (PureF result1) (PureF result2) = eqResult result1 result2
  liftEq2 _ eqRecur (BindF step1 yield1) (BindF step2 yield2) = liftEq (\ x1 x2 -> eqRecur (yield1 x1) (yield2 x2)) step1 step2
  liftEq2 _ _ _ _ = False

instance (Eq1 f, Eq a) => Eq1 (FreerF f a) where
  liftEq = liftEq2 (==)

instance (Eq1 f, Eq a, Eq b) => Eq (FreerF f a b) where
  (==) = liftEq (==)


instance Show1 f => Show2 (FreerF f) where
  liftShowsPrec2 sp1 _ _ _ d (PureF result) = showsUnaryWith sp1 "PureF" d result
  liftShowsPrec2 sp1 _ sp2 sa2 d (BindF step yield) = showsBinaryWith (liftShowsPrec ((. yield) . sp2) (sa2 . fmap yield)) (const showString) "BindF" d step "_"

instance (Show1 f, Show a) => Show1 (FreerF f a) where
  liftShowsPrec = liftShowsPrec2 showsPrec showList

instance (Show1 f, Show a, Show b) => Show (FreerF f a b) where
  showsPrec = liftShowsPrec showsPrec showList


type instance Base (Freer f a) = FreerF f a

instance Recursive (Freer f a) where
  project (Pure a) = PureF a
  project (Bind r t) = BindF r t
  -- INLINE project --

instance Corecursive (Freer f a) where
  embed (PureF a) = Pure a
  embed (BindF r t) = Bind r t
  -- INLINE embed --
--
-- INLINE hoistFreer 
-}