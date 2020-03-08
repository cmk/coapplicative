{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TupleSections #-}
{-# Language ConstraintKinds #-}
{-# Language FlexibleContexts #-}
{-# Language FlexibleInstances #-}
{-# Language TypeOperators #-}

module Data.Functor.Coapply (
  -- * Coapply
    Coapply(..)
  , apply
  , select
  , coselect
  , coeval
  , appendl
  , concatl
  , concatr
  , concatl'
  , concatr'
  -- * Select
  , Select
  , eitherS
  , branch
  , bindBool
  -- * Distributive1
  , Distributive1(..)
  , cotraverse1
) where

import Control.Arrow
import Control.Monad.Trans.Reader
import Data.Bifunctor
import Data.Bool
import Data.Coerce
import Data.Foldable (foldr')
import Data.Foldable (foldr)
import Data.Functor.Apply
import Data.Functor.Compose
import Data.Functor.Const
import Data.Functor.Identity
import Data.Functor.Product
import Data.List.NonEmpty (NonEmpty(..))
import Data.Tagged
import Test.Logic hiding (apply)

import GHC.Generics (U1(..), (:*:)(..), (:.:)(..), Par1(..)) -- , Rec1(..), M1(..)


{-
foo :: Coapplicative f => (a -> c) -> (b -> c) -> f (Either a b) -> c
foo f g = either (f . copure) (g . copure) . coapply

foo' :: Coapplicative f => (a -> c) -> (b -> c) -> f (Either a b) -> c
foo' f g = either f g . copure

--TODO refactor w/ idempotent prop
coapplyl :: Coapply f => f a -> f a + f b
coapplyl = coapply . fmap Left

coevall' :: Coapply f => f a -> f (a + b)
coevall' = coeval . fmap Left

coapplyr :: Coapply f => f b -> f a + f b
coapplyr = coapply . fmap Right

coevalr' :: Coapply f => f b -> f (a + b)
coevalr' = coeval . fmap Right
-}

---------------------------------------------------------------------
-- Coapply
---------------------------------------------------------------------

-- |
--
-- @
-- 'coapply' . 'fmap' 'Left' = 'Left'
-- 'coeval' . 'fmap' 'Left' = 'fmap' 'Left'
-- 'coeval' . 'fmap' 'Right' = 'fmap' 'Right'
-- @
--
class Functor f => Coapply f where
  coapply :: f (a + b) -> (f a + f b)

apply :: Apply f => (f a , f b) -> f (a , b)
apply = uncurry $ liftF2 (,)

select :: Functor f => f (a , b) -> (f a , f b)
select = fmap fst &&& fmap snd

coselect :: Functor f => (f a + f b) -> f (a + b) 
coselect = fmap Left ||| fmap Right

-- | Evaluate a coapplicative expression, exiting on the first 'Left' if it exists.
--
-- >>> coeval $ Left "foo" :| [Right "bar"]
-- Left "foo" :| []
-- >>> coeval $ Right "foo" :| [Right "bar"]
-- Right "foo" :| [Right "bar"]
--
coeval :: Coapply f => f (a + b) -> f (a + b)
coeval = coselect . coapply

-- | Append two semigroup values or return the @Right@ one.
appendl :: Semigroup a => a -> a + b -> a + b
appendl a1 (Left a2) = Left (a1 <> a2)
appendl _  (Right b) = Right b

concatl :: [a + b] -> [a]
concatl = foldr (either (:) (const id)) []

concatr :: [a + b] -> [b]
concatr = foldr (either (const id) (:)) []

concatl' :: [a + b] -> [a]
concatl' = foldr' (either (:) (const id)) []

concatr' :: [a + b] -> [b]
concatr' = foldr' (either (const id) (:)) []

---------------------------------------------------------------------
-- Select
---------------------------------------------------------------------

type Select f = (Coapply f, Apply f)

eitherS :: Select f => f (a + b) -> f (a -> c) -> f (b -> c) -> f c
eitherS ab f g = either (f <.>) (g <.>) $ coapply ab

-- | Branch on a boolean value, skipping unnecessary effects.
--
-- >>> head $ branch (True :| []) (print "foo" :| []) (print "bar" :| [])
-- "foo"
--
branch :: Select f => f Bool -> f a -> f a -> f a
branch x t e = eitherS (bool (Right ()) (Left ()) <$> x) (const <$> t) (const <$> e)

bindBool :: Select f => f Bool -> (Bool -> f a) -> f a
bindBool x f = branch x (f False) (f True)

---------------------------------------------------------------------
-- Distributive1
---------------------------------------------------------------------

class Functor g => Distributive1 g where
  {-# MINIMAL distribute1 | collect1 #-}
  
  -- | The dual of 'Data.Semigroup.Traversable.sequence1'
  --
  -- @
  -- 'distribute1' = 'collect1' 'id'
  -- 'distribute1' . 'distribute1' = 'id'
  -- @
  distribute1 :: Coapply f => f (g a) -> g (f a)
  distribute1 = collect1 id

  -- |
  -- @
  -- 'collect1' f = 'distribute1' . 'fmap' f
  -- 'fmap' f = 'runIdentity' . 'collect1' ('Identity' . f)
  -- 'fmap' 'distribute1' . 'collect1' f = 'getCompose' . 'collect1' ('Compose' . f)
  -- @
  collect1 :: Coapply f => (a -> g b) -> f a -> g (f b)
  collect1 f = distribute1 . fmap f

-- | The dual of 'Data.Semigroup.Traversable.traverse1'
--
-- @
-- 'cotraverse1' f = 'fmap' f . 'distribute1'
-- @
cotraverse1 :: Coapply f => Distributive1 g => (f a -> b) -> f (g a) -> g b
cotraverse1 f = fmap f . distribute1

---------------------------------------------------------------------
-- Instances
---------------------------------------------------------------------

instance Coapply Identity where
  coapply (Identity ab) = either (Left . Identity) (Right . Identity) ab

instance Coapply (Const r) where
  coapply (Const r) = Left (Const r)

instance Coapply (Tagged k) where
  coapply (Tagged ab) = either (Left . Tagged) (Right . Tagged) ab

instance Coapply Maybe where
  coapply Nothing = Left Nothing
  coapply (Just e) = bimap pure pure e

instance Coapply [] where
  coapply [] = Left []
  coapply (Left x : es) = Left $ x : concatl' es
  coapply (Right y : es) = Right $ y : concatr' es

instance Coapply NonEmpty where
  coapply (Left x :| es) = Left $ x :| concatl' es
  coapply (Right y :| es) = Right $ y :| concatr' es

instance Coapply ((,) r) where
  coapply (r, a) = either (Left . (r,)) (Right . (r,)) a

instance Monoid r => Coapply ((->) r) where
  coapply f = either (Left . const) (Right . const) $ f mempty

--instance Monoid m => Coapply (ReaderT r m) where

instance (Coapply f, Coapply g) => Coapply (Compose f g) where
  coapply (Compose ab) = bimap Compose Compose . coapply . fmap coapply $ ab


--TODO: push upstream?
--instance Distributive (Either e) where
--  distribute' = first copure . coapply

instance Distributive1 Identity where
  distribute1 = Identity . fmap runIdentity

instance Distributive1 (Tagged t) where
  distribute1 = Tagged . fmap unTagged

instance Distributive1 Maybe where
  distribute1 = either l r . coapply . fmap proj where
    l = const Nothing
    r = Just
    proj = maybe (Left ()) Right

-- >>> distribute1 ["hi","jk"]
-- ["hj","ik"]
instance Distributive1 [] where
  distribute1 = either l r . coapply . fmap proj where
    l = const []
    r f = (fst $ select f) : (distribute1 . snd $ select f)
    proj [] = Left ()
    proj (x:xs) = Right (x, xs)

-- >>> distribute1 $ ('h' :| ['i']) :| [('j' :| ['k'])]
-- ('h' :| "j") :| ['i' :| "k"]
instance Distributive1 NonEmpty where
  distribute1 = either l r . coapply . fmap proj where
    l = pure
    r f = (fst $ select f) :| (distribute1 . snd $ select f)
    proj (x :| []) = Left x
    proj (x :| xs) = Right (x, xs)

instance Distributive1 ((->) r) where
  distribute1 a e = fmap ($e) a
  collect1 f q e = fmap (flip f e) q

instance Distributive1 m => Distributive1 (ReaderT r m) where
  distribute1 a = ReaderT $ \e -> collect1 (flip runReaderT e) a
  collect1 f x = ReaderT $ \e -> collect1 (\a -> runReaderT (f a) e) x

instance (Distributive1 f, Distributive1 g) => Distributive1 (Product f g) where
  -- It might be tempting to write a 'collect1' implementation that
  -- composes the passed function with fstP and sndP. This could be bad,
  -- because it would lead to the passed function being evaluated twice
  -- for each element of the underlying functor.
  distribute1 wp = Pair (collect1 fstP wp) (collect1 sndP wp) where
    fstP (Pair a _) = a
    sndP (Pair _ b) = b

instance Distributive1 U1 where
  distribute1 _ = U1

instance (Distributive1 a, Distributive1 b) => Distributive1 (a :*: b) where
  -- It might be tempting to write a 'collect' implementation that
  -- composes the passed function with fstP and sndP. This could be bad,
  -- because it would lead to the passed function being evaluated twice
  -- for each element of the underlying functor.
  distribute1 f = collect1 fstP f :*: collect1 sndP f where
    fstP (l :*: _) = l
    sndP (_ :*: r) = r

instance (Distributive1 a, Distributive1 b) => Distributive1 (a :.: b) where
  distribute1 = Comp1 . fmap distribute1 . collect1 unComp1
  collect1 f = Comp1 . fmap distribute1 . collect1 (coerce f)

instance Distributive1 Par1 where
  distribute1 = Par1 . fmap unPar1
  collect1 = coerce (fmap :: (a -> b) -> f a -> f b)
    :: forall f a b . Functor f => (a -> Par1 b) -> f a -> Par1 (f b)

{-
instance Distributive1 f => Distributive1 (Rec1 f) where
  distribute1 = Rec1 . collect1 unRec1
  collect1 = coerce (collect1 :: (a -> f b) -> g a -> f (g b))
    :: forall g a b . Functor g
    => (a -> Rec1 f b) -> g a -> Rec1 f (g b)

instance Distributive1 f => Distributive1 (M1 i c f) where
  distribute1 = M1 . collect1 unM1
  collect1 = coerce (collect1 :: (a -> f b) -> g a -> f (g b))
    :: forall g a b . Functor g
    => (a -> M1 i c f b) -> g a -> M1 i c f (g b)
-}
