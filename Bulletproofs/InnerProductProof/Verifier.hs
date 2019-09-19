{-# LANGUAGE RecordWildCards, NamedFieldPuns, MultiWayIf, ScopedTypeVariables #-}

module Bulletproofs.InnerProductProof.Verifier (
  verifyProof,
) where

import Protolude

import qualified Data.List as L
import qualified Data.Map as Map
import Data.Curve.Weierstrass.SECP256K1 (PA, Fr)
import Data.Curve.Weierstrass hiding (char)

import Bulletproofs.Utils

import Bulletproofs.InnerProductProof.Internal

-- | Optimized non-interactive verifier using multi-exponentiation and batch verification
verifyProof
  :: Integer            -- ^ Range upper bound
  -> InnerProductBase PA  -- ^ Generators Gs, Hs, h
  -> PA       -- ^ Commitment P
  -> InnerProductProof Fr PA
  -- ^ Proof that a secret committed value lies in a certain interval
  -> Bool
verifyProof n productBase@InnerProductBase{..} commitmentLR productProof@InnerProductProof{ l, r }
  = c == cProof
  where
    (challenges, _invChallenges, c) = mkChallenges productProof commitmentLR
    otherExponents = mkOtherExponents n challenges
    cProof
      = (gsCommit `mul` l)
        `add`
        (hsCommit `mul` r)
        `add`
        (bH `mul` (l * r) )

    gsCommit = sumExps otherExponents bGs
    hsCommit = sumExps (reverse otherExponents) bHs

mkChallenges
  :: InnerProductProof Fr PA
  -> PA
  -> ([Fr], [Fr], PA)
mkChallenges InnerProductProof{ lCommits, rCommits } commitmentLR
  = foldl'
      (\(xs, xsInv, accC) (li, ri)
        -> let x = shamirX' accC li ri
               xInv = recip x
               c = (li `mul` (x ^ 2)) `add` (ri `mul` (xInv ^ 2)) `add` accC
           in (x:xs, xInv:xsInv, c)
      )
      ([], [], commitmentLR)
      (zip lCommits rCommits)

mkOtherExponents :: Integer -> [Fr] -> [Fr]
mkOtherExponents n challenges
  = Map.elems $ foldl'
      f
      (Map.fromList [(0, recip $ product challenges)])
      [0..n'-1]
  where
    n' = n `div` 2
    f acc i = foldl' (f' i) acc [0..logBase2 n-1]

    f' :: Integer -> Map.Map Integer Fr -> Integer -> Map.Map Integer Fr
    f' i acc' j
      = let i1 = (2^j) + i in
          if | i1 >= n -> acc'
             | Map.member i1 acc' -> acc'
             | otherwise -> Map.insert
                              i1
                              (acc' Map.! i * ((challenges L.!! fromIntegral j) ^ 2))
                              acc'


