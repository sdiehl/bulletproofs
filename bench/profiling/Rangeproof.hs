{-# LANGUAGE NoImplicitPrelude #-}

-- In order to get profiling data, we first need to run (in the parent
-- directory of this file):
--
--   stack build --library-profiling
--
-- then to profile the execution of this module, we run:
--
--   stack ghc -- -prof -fprof-auto -rtsopts bench/profiling/Rangeproof.hs -o Rangeproof
--   ./Rangeproof +RTS -p
--
-- and look at the output in the file "Rangeproof.prof"

module Main where

import Protolude

import qualified Bulletproofs.RangeProof as RP
import qualified Bulletproofs.Utils as Utils
import qualified Bulletproofs.Fq as Fq

main :: IO ()
main = do
  let upperBound = 2 ^ (2 ^ 6)
      input = 7238283
      inputBlinding = 827361
      commitment = Utils.commit input inputBlinding
  Right proof <- runExceptT $ RP.generateProof upperBound (input, inputBlinding)
  print $ RP.verifyProof upperBound commitment (proof :: RP.RangeProof Fq.Fq)
