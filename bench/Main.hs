-- To run this, run "stack bench"

module Main where

import Protolude
import Criterion.Main

import qualified Bench.RangeProof as RP
import qualified Bench.ArithCircuit as AC

main :: IO ()
main = defaultMain
  [ bgroup "Rangeproof" RP.benchmark
  , bgroup "Arithmetic circuit" AC.benchmark
  ]
