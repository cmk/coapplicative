{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Test.Prop.Coapplicative (props) where

import Hedgehog

import Control.Coapplicative
import Data.Functor.Compose (Compose)
import Data.Functor.Identity (Identity)
import Data.Tagged (Tagged)

import qualified Test.Gen as G

-- | coapply . fmap Right = Right
prop_coapply_right
  :: forall f. (Coapplicative f, Eq (f Int), Show (f Int))
  => Gen (f Int) -> Property
prop_coapply_right gen = property $ do
  fb <- forAll gen
  let fab = fmap Right fb :: f (Either Int Int)
  coapply fab === Right fb

-- | either (f . copure) (g . copure) . coapply = either f g . copure
prop_copure_coapply
  :: forall f. (Coapplicative f, Show (f (Either Int Int)))
  => Gen (f (Either Int Int)) -> Property
prop_copure_coapply gen = property $ do
  fab <- forAll gen
  let f = negate
      g = (+ 1)
  (either (f . copure) (g . copure) . coapply) fab === (either f g . copure) fab

props :: Group
props = Group "Coapplicative"
  -- Identity
  [ ("coapply_right/Identity",    prop_coapply_right  (G.identity G.int))
  , ("copure_coapply/Identity",   prop_copure_coapply (G.identity (G.either' G.int G.int)))
  -- Tagged
  , ("coapply_right/Tagged",      prop_coapply_right  (G.tagged G.int :: Gen (Tagged () Int)))
  , ("copure_coapply/Tagged",     prop_copure_coapply (G.tagged (G.either' G.int G.int) :: Gen (Tagged () (Either Int Int))))
  -- (,) String
  , ("coapply_right/Pair",        prop_coapply_right  (G.pair G.string G.int))
  , ("copure_coapply/Pair",       prop_copure_coapply (G.pair G.string (G.either' G.int G.int)))
  -- NonEmpty
  , ("coapply_right/NonEmpty",    prop_coapply_right  (G.nonEmpty G.int))
  , ("copure_coapply/NonEmpty",   prop_copure_coapply (G.nonEmpty (G.either' G.int G.int)))
  -- Compose Identity Identity
  , ("coapply_right/Compose",     prop_coapply_right  (G.compose (G.identity (G.identity G.int)) :: Gen (Compose Identity Identity Int)))
  , ("copure_coapply/Compose",    prop_copure_coapply (G.compose (G.identity (G.identity (G.either' G.int G.int))) :: Gen (Compose Identity Identity (Either Int Int))))
  ]
