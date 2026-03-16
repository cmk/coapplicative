module Test.Gen
  ( int
  , string
  , either'
  , identity
  , tagged
  , maybe'
  , list
  , nonEmpty
  , pair
  , const'
  , compose
  ) where

import Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import Data.Functor.Compose (Compose(..))
import Data.Functor.Const (Const(..))
import Data.Functor.Identity (Identity(..))
import Data.List.NonEmpty (NonEmpty(..))
import Data.Tagged (Tagged(..))

int :: Gen Int
int = Gen.int (Range.linear (-100) 100)

string :: Gen String
string = Gen.string (Range.linear 0 10) Gen.alpha

either' :: Gen a -> Gen b -> Gen (Either a b)
either' ga gb = Gen.choice [Left <$> ga, Right <$> gb]

identity :: Gen a -> Gen (Identity a)
identity = fmap Identity

tagged :: Gen a -> Gen (Tagged k a)
tagged = fmap Tagged

maybe' :: Gen a -> Gen (Maybe a)
maybe' = Gen.maybe

list :: Gen a -> Gen [a]
list = Gen.list (Range.linear 0 10)

nonEmpty :: Gen a -> Gen (NonEmpty a)
nonEmpty g = (:|) <$> g <*> Gen.list (Range.linear 0 9) g

pair :: Gen r -> Gen a -> Gen (r, a)
pair gr ga = (,) <$> gr <*> ga

const' :: Gen r -> Gen (Const r a)
const' = fmap Const

compose :: Gen (f (g a)) -> Gen (Compose f g a)
compose = fmap Compose
