{-# LANGUAGE RecordWildCards, NamedFieldPuns, MultiWayIf #-}

module Bulletproofs.InnerProductProof.Verifier
  ( verifyProof
  ) where

import Protolude

import qualified Data.List as L
import qualified Data.Map as Map

import qualified Crypto.PubKey.ECC.Types as Crypto

import Bulletproofs.Curve
import Bulletproofs.Utils
import Bulletproofs.Fq as Fq

import Bulletproofs.RangeProof.Internal
import Bulletproofs.InnerProductProof.Internal

-- | Optimized non-interactive verifier using multi-exponentiation and batch verification
verifyProof
  :: Integer            -- ^ Range upper bound
  -> InnerProductBase   -- ^ Generators Gs, Hs, h
  -> Crypto.Point       -- ^ Commitment P
  -> InnerProductProof
  -- ^ Proof that a secret committed value lies in a certain interval
  -> Bool
verifyProof n productBase@InnerProductBase{..} commitmentLR productProof@InnerProductProof{ l, r }
  = c == cProof
  where
    (challenges, invChallenges, c) = mkChallenges productProof commitmentLR
    otherExponents = mkOtherExponents n challenges
    cProof
      = (l `mulP` gsCommit)
        `addP`
        (r `mulP` hsCommit)
        `addP`
        ((l * r) `mulP` bH)

    gsCommit = foldl' addP Crypto.PointO (zipWith mulP otherExponents bGs)
    hsCommit = foldl' addP Crypto.PointO (zipWith mulP (reverse otherExponents) bHs)

mkChallenges :: InnerProductProof -> Crypto.Point -> ([Fq], [Fq], Crypto.Point)
mkChallenges InnerProductProof{ lCommits, rCommits } commitmentLR
  = foldl'
      (\(xs, xsInv, accC) (li, ri)
        -> let x = shamirX' accC li ri
               xInv = inv x
               c = (fqSquare x `mulP` li) `addP` (fqSquare xInv `mulP` ri) `addP` accC
           in (x:xs, xInv:xsInv, c)
      )
      ([], [], commitmentLR)
      (zip lCommits rCommits)

mkOtherExponents :: Integer -> [Fq] -> [Fq]
mkOtherExponents n challenges
  = Map.elems $ foldl'
      f
      (Map.fromList [(0, Fq.inv $ product challenges)])
      [0..n'-1]
  where
    n' = n `div` 2
    f acc i = foldl' (f' i) acc [0..logBase2 n-1]
    f' :: Integer -> Map.Map Integer Fq -> Integer -> Map.Map Integer Fq
    f' i acc' j
      = let i1 = (2^j) + i in
          if | i1 >= n -> acc'
             | Map.member i1 acc' -> acc'
             | otherwise -> Map.insert
                              i1
                              (acc' Map.! i * fqSquare (challenges L.!! fromIntegral j))
                              acc'


