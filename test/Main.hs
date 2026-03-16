module Main (main) where

import Hedgehog (checkParallel)
import System.Exit (exitFailure)

import qualified Test.Prop.Coapply as Coapply
import qualified Test.Prop.Coapplicative as Coapplicative
import qualified Test.Prop.Distributive1 as Distributive1

main :: IO ()
main = do
  results <- sequence
    [ checkParallel Coapply.props
    , checkParallel Coapplicative.props
    , checkParallel Distributive1.props
    ]
  if and results then pure () else exitFailure
