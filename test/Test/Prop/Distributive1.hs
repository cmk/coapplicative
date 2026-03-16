{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Test.Prop.Distributive1 (props) where

import Hedgehog

import Data.Functor.Coapply
import Data.Functor.Identity (Identity)
import Data.Tagged (Tagged)

import qualified Test.Gen as G

-- | distribute1 . distribute1 = id
prop_involution
  :: forall f g.
     ( Distributive1 g, Coapply f
     , Distributive1 f, Coapply g
     , Eq (f (g Int)), Show (f (g Int))
     )
  => Gen (f (g Int)) -> Property
prop_involution gen = property $ do
  fga <- forAll gen
  (distribute1 . distribute1) fga === fga

-- | collect1 id = distribute1
prop_collect1_id
  :: forall f g.
     ( Distributive1 g, Coapply f
     , Eq (g (f Int)), Show (g (f Int)), Show (f (g Int))
     )
  => Gen (f (g Int)) -> Property
prop_collect1_id gen = property $ do
  fga <- forAll gen
  collect1 id fga === distribute1 fga

props :: Group
props = Group "Distributive1"
  -- Identity / Identity
  [ ("involution/Identity_Identity",  prop_involution  (G.identity (G.identity G.int)))
  , ("collect1_id/Identity_Identity", prop_collect1_id (G.identity (G.identity G.int)))
  -- Identity / Maybe
  , ("involution/Identity_Maybe",     prop_involution  (G.identity (G.maybe' G.int)))
  , ("collect1_id/Identity_Maybe",    prop_collect1_id (G.identity (G.maybe' G.int)))
  -- Identity / Tagged
  , ("involution/Identity_Tagged",    prop_involution  (G.identity (G.tagged G.int) :: Gen (Identity (Tagged () Int))))
  , ("collect1_id/Identity_Tagged",   prop_collect1_id (G.identity (G.tagged G.int) :: Gen (Identity (Tagged () Int))))
  -- Identity / NonEmpty
  , ("involution/Identity_NonEmpty",  prop_involution  (G.identity (G.nonEmpty G.int)))
  , ("collect1_id/Identity_NonEmpty", prop_collect1_id (G.identity (G.nonEmpty G.int)))
  -- Identity / List
  , ("involution/Identity_List",      prop_involution  (G.identity (G.list G.int)))
  , ("collect1_id/Identity_List",     prop_collect1_id (G.identity (G.list G.int)))
  -- Maybe / Identity
  , ("involution/Maybe_Identity",     prop_involution  (G.maybe' (G.identity G.int)))
  , ("collect1_id/Maybe_Identity",    prop_collect1_id (G.maybe' (G.identity G.int)))
  -- NonEmpty / Identity
  , ("involution/NonEmpty_Identity",  prop_involution  (G.nonEmpty (G.identity G.int)))
  , ("collect1_id/NonEmpty_Identity", prop_collect1_id (G.nonEmpty (G.identity G.int)))
  -- Tagged / Identity
  , ("involution/Tagged_Identity",    prop_involution  (G.tagged (G.identity G.int) :: Gen (Tagged () (Identity Int))))
  , ("collect1_id/Tagged_Identity",   prop_collect1_id (G.tagged (G.identity G.int) :: Gen (Tagged () (Identity Int))))
  ]
