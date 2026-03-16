{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Test.Prop.Coapply (props) where

import Hedgehog

import Data.Functor.Coapply
import Data.Functor.Compose (Compose)
import Data.Functor.Const (Const)
import Data.Functor.Identity (Identity)
import Data.Tagged (Tagged)

import qualified Test.Gen as G

-- | coapply . fmap Left = Left
prop_coapply_left
  :: forall f. (Coapply f, Eq (f Int), Show (f Int))
  => Gen (f Int) -> Property
prop_coapply_left gen = property $ do
  fa <- forAll gen
  let fab = fmap Left fa :: f (Either Int Int)
  coapply fab === Left fa

-- | coeval . fmap Left = fmap Left
prop_coeval_left
  :: forall f. (Coapply f, Eq (f (Either Int Int)), Show (f (Either Int Int)), Show (f Int))
  => Gen (f Int) -> Property
prop_coeval_left gen = property $ do
  fa <- forAll gen
  let fab = fmap Left fa :: f (Either Int Int)
  coeval fab === fab

-- | coeval . fmap Right = fmap Right
prop_coeval_right
  :: forall f. (Coapply f, Eq (f (Either Int Int)), Show (f (Either Int Int)), Show (f Int))
  => Gen (f Int) -> Property
prop_coeval_right gen = property $ do
  fa <- forAll gen
  let fab = fmap Right fa :: f (Either Int Int)
  coeval fab === fab

props :: Group
props = Group "Coapply"
  -- Identity
  [ ("coapply_left/Identity",  prop_coapply_left  (G.identity G.int))
  , ("coeval_left/Identity",   prop_coeval_left   (G.identity G.int))
  , ("coeval_right/Identity",  prop_coeval_right  (G.identity G.int))
  -- Tagged
  , ("coapply_left/Tagged",    prop_coapply_left  (G.tagged G.int :: Gen (Tagged () Int)))
  , ("coeval_left/Tagged",     prop_coeval_left   (G.tagged G.int :: Gen (Tagged () Int)))
  , ("coeval_right/Tagged",    prop_coeval_right  (G.tagged G.int :: Gen (Tagged () Int)))
  -- Maybe
  , ("coapply_left/Maybe",     prop_coapply_left  (G.maybe' G.int))
  , ("coeval_left/Maybe",      prop_coeval_left   (G.maybe' G.int))
  , ("coeval_right/Maybe",     prop_coeval_right  (G.maybe' G.int))
  -- List
  , ("coapply_left/List",      prop_coapply_left  (G.list G.int))
  , ("coeval_left/List",       prop_coeval_left   (G.list G.int))
  , ("coeval_right/List",      prop_coeval_right  (G.list G.int))
  -- NonEmpty
  , ("coapply_left/NonEmpty",  prop_coapply_left  (G.nonEmpty G.int))
  , ("coeval_left/NonEmpty",   prop_coeval_left   (G.nonEmpty G.int))
  , ("coeval_right/NonEmpty",  prop_coeval_right  (G.nonEmpty G.int))
  -- (,) String
  , ("coapply_left/Pair",      prop_coapply_left  (G.pair G.string G.int))
  , ("coeval_left/Pair",       prop_coeval_left   (G.pair G.string G.int))
  , ("coeval_right/Pair",      prop_coeval_right  (G.pair G.string G.int))
  -- Const String
  , ("coapply_left/Const",     prop_coapply_left  (G.const' G.string :: Gen (Const String Int)))
  , ("coeval_left/Const",      prop_coeval_left   (G.const' G.string :: Gen (Const String Int)))
  , ("coeval_right/Const",     prop_coeval_right  (G.const' G.string :: Gen (Const String Int)))
  -- Compose Identity Maybe
  , ("coapply_left/Compose",   prop_coapply_left  (G.compose (G.identity (G.maybe' G.int)) :: Gen (Compose Identity Maybe Int)))
  , ("coeval_left/Compose",    prop_coeval_left   (G.compose (G.identity (G.maybe' G.int)) :: Gen (Compose Identity Maybe Int)))
  , ("coeval_right/Compose",   prop_coeval_right  (G.compose (G.identity (G.maybe' G.int)) :: Gen (Compose Identity Maybe Int)))
  ]
