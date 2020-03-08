{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TupleSections #-}
{-# Language ConstraintKinds #-}
{-# Language FlexibleContexts #-}
{-# Language FlexibleInstances #-}
{-# Language TypeOperators #-}

module Control.Coapplicative (
    Applicative'
  -- * Coapplicative
  , Coapplicative(..)
  -- * Coapply
  , Coapply(..)
  , apply
  , select
  , coselect
  , coeval
  -- * Select
  , Select
  , eitherS
  , branch
  , bindBool
  -- * Selective
  , Selective
  , apS
  , (<*?)
  , eliminate
  , whenS
  , whileS
  , fromMaybeS
  , untilRight
  , (<||>)
  , (<&&>)
  , anyS
  , allS
  , foldS
  , orElse
  , andAlso
  , appendl
) where

--import Control.Monad.Trans.Reader
import Data.Bool
import Data.Function ((&))
import Data.Functor.Apply
import Data.Functor.Coapply as Export
import Data.Functor.Compose
import Data.Functor.Identity
import Data.List.NonEmpty (NonEmpty(..))
import Data.Tagged
import Test.Logic hiding (apply)

import qualified Data.List.NonEmpty as L1


type Applicative' f = (Apply f, Applicative f)

---------------------------------------------------------------------
-- Coapplicative
---------------------------------------------------------------------

-- |
--
-- @
-- 'coapply' . 'fmap' 'Right' = 'Right'
-- 'either' (f . 'copure') (g . 'copure') . 'coapply' = 'either' f g . 'copure'
-- @
--
class Coapply f => Coapplicative f where
  -- 
  copure :: f a -> a

---------------------------------------------------------------------
-- Selective
---------------------------------------------------------------------

type Selective f = (Coapply f, Applicative' f)

{-| Recover the application operator '<*>' from '<*?'. /Rigid/ selective
functors satisfy the law '<*>' @=@ 'apS' and furthermore, the resulting
applicative functor satisfies all laws of 'Applicative':

* Identity:

    > pure id <*> v = v

* Homomorphism:

    > pure f <*> pure x = pure (f x)

* Interchange:

    > u <*> pure y = pure ($y) <*> u

* Composition:

    > (.) <$> u <*> v <*> w = u <*> (v <*> w)
-}
apS :: Selective f => f (a -> b) -> f a -> f b
apS f x = (Left <$> f) <*? ((&) <$> x)



{-
coeval :: b -> (b -> a) + a -> a
coeval b = either ($ b) id
{-# INLINE coeval #-}


f :: String -> Either Float String
f i = if i == "ten" then Left 10.0 else Right i
-}
 
infixl 4 <*?

-- | 
--
-- (Right "foo" :| [Right "bar"]) <*? (pure $ const "baz")
-- "foo" :| ["bar"]
-- (Left "foo" :| [Right "bar"]) <*? (pure $ const "baz")
-- "baz" :| []
--
-- See < http://hackage.haskell.org/package/selective/docs/Control-Selective.html >
--
(<*?) :: Selective f => f (a + b) -> f (a -> b) -> f b
(<*?) ab f = eitherS ab f $ pure id

-- | Eliminate the @a@ from @f (a + b)@ and replace with the provided @f b@.
-- 
-- >>> eliminate 1.0 ["foo","bar"] [Left 1.0] :: [Float + String]
-- [Right "foo",Right "bar"]
-- >>> eliminate 1.0 ["foo","bar"] [Left 3.4] :: [Float + String]
-- [Left 3.4]
-- 
eliminate :: Eq a => Selective f => a -> f b -> f (a + b) -> f (a + b)
eliminate a fb fa = fmap (match a) fa <*? fmap (const . Right) fb
  where
    match _ (Right y) = Right (Right y)
    match x (Left  y) = if x == y then Left () else Right (Left y)

-- | Conditionally perform an effect.
whenS :: Selective f => f Bool -> f () -> f ()
whenS x y = (bool (Right ()) (Left ()) <$> x) <*? (const <$> y)

-- | Keep checking an effectful condition while it holds.
whileS :: Selective f => f Bool -> f ()
whileS act = whenS act (whileS act)

-- | A lifted version of 'Data.Maybe.fromMaybe'.
fromMaybeS :: Selective f => f a -> f (Maybe a) -> f a
fromMaybeS x mx = fmap (maybe (Left ()) Right) mx <*? fmap const x

-- | Keep running an effectful computation until it returns a @Right@ value,
-- collecting the @Left@'s using a supplied @Monoid@ instance.
untilRight :: Monoid a => Selective f => f (a + b) -> f (a , b)
untilRight x = y <*? h
  where
    -- y :: f (Either a (a, b))
    y = fmap (mempty,) <$> x
    -- h :: f (a -> (a, b))
    h = (\(as, b) a -> (mappend a as, b)) <$> untilRight x

-- | A lifted version of lazy Boolean OR.
(<||>) :: Selective f => f Bool -> f Bool -> f Bool
a <||> b = branch a (pure True) b

-- | A lifted version of lazy Boolean AND.
(<&&>) :: Selective f => f Bool -> f Bool -> f Bool
a <&&> b = branch a b (pure False)

-- | A lifted version of 'any'. Retains the short-circuiting behaviour.
anyS :: Selective f => (a -> f Bool) -> [a] -> f Bool
anyS p = foldr ((<||>) . p) (pure False)

-- | A lifted version of 'all'. Retains the short-circuiting behaviour.
allS :: Selective f => (a -> f Bool) -> [a] -> f Bool
allS p = foldr ((<&&>) . p) (pure True)

-- | Generalised folding with the short-circuiting behaviour.
foldS :: (Selective f, Foldable t, Monoid b) => t (f (a + b)) -> f (a + b)
foldS = foldr andAlso (pure (Right mempty))

-- | Return the first @Right@ value. If both are @Left@'s, accumulate errors.
orElse :: Semigroup a => Selective f => f (a + b) -> f (a + b) -> f (a + b)
orElse x y = eitherS x (flip appendl <$> y) (pure Right)

-- | Accumulate the @Right@ values, or return the first @Left@.
-- 
-- >>> andAlso [Right "foo", Right "bar", Right "baz"] [Right "!"]
-- [Right "foo!",Right "bar!",Right "baz!"]
-- >>> andAlso [Right "foo", Right "bar", Left 'e'] [Right "!"]
-- [Right "foo!",Right "bar!"]
-- >>> andAlso [Right "foo", Right "bar", Left 'e'] [Left 'f']
-- [Left 'f',Left 'f']
-- 
andAlso :: Semigroup b => Selective f => f (a + b) -> f (a + b) -> f (a + b)
andAlso x y = eswap <$> orElse (eswap <$> x) (eswap <$> y)

---------------------------------------------------------------------
-- Instances
---------------------------------------------------------------------

instance Coapplicative Identity where
  copure (Identity a) = a

instance Coapplicative (Tagged k) where
  copure (Tagged a) = a

instance Coapplicative ((,) r) where
  copure (_, a) = a

instance Monoid r => Coapplicative ((->) r) where
  copure f = f mempty

--instance Monoid r => Coapplicative (ReaderT r m) where

instance Coapplicative NonEmpty where
  copure = L1.head

instance (Coapplicative f, Coapplicative g) => Coapplicative (Compose f g) where
  copure (Compose a) = copure . fmap copure $ a
