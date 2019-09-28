module Main where

import Protolude

import qualified Example.ArithmeticCircuit as AC
import qualified Example.RangeProof as RP

main :: IO ()
main = do
  RP.runExamples
  AC.runExample
