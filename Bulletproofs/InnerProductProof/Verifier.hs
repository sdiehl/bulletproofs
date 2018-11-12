{-# LANGUAGE RecordWildCards, NamedFieldPuns, MultiWayIf, ScopedTypeVariables #-}

module Bulletproofs.InnerProductProof.Verifier (
  verifyProof,
) where

import Protolude

import qualified Data.List as L
import qualified Data.Map as Map

import qualified Crypto.PubKey.ECC.Types as Crypto

import Bulletproofs.Curve
import Bulletproofs.Utils

import Bulletproofs.InnerProductProof.Internal

-- | Optimized non-interactive verifier using multi-exponentiation and batch verification
verifyProof
  :: (AsInteger f, Field f)
  => Integer            -- ^ Range upper bound
  -> InnerProductBase   -- ^ Generators Gs, Hs, h
  -> Crypto.Point       -- ^ Commitment P
  -> InnerProductProof f
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

    gsCommit = sumExps otherExponents bGs
    hsCommit = sumExps (reverse otherExponents) bHs

mkChallenges :: (AsInteger f, Field f) => InnerProductProof f -> Crypto.Point -> ([f], [f], Crypto.Point)
mkChallenges InnerProductProof{ lCommits, rCommits } commitmentLR
  = foldl'
      (\(xs, xsInv, accC) (li, ri)
        -> let x = shamirX' accC li ri
               xInv = recip x
               c = (fSquare x `mulP` li) `addP` (fSquare xInv `mulP` ri) `addP` accC
           in (x:xs, xInv:xsInv, c)
      )
      ([], [], commitmentLR)
      (zip lCommits rCommits)

mkOtherExponents :: forall f . (AsInteger f, Field f) => Integer -> [f] -> [f]
mkOtherExponents n challenges
  = Map.elems $ foldl'
      f
      (Map.fromList [(0, recip $ product challenges)])
      [0..n'-1]
  where
    n' = n `div` 2
    f acc i = foldl' (f' i) acc [0..logBase2 n-1]

    f' :: Integer -> Map.Map Integer f -> Integer -> Map.Map Integer f
    f' i acc' j
      = let i1 = (2^j) + i in
          if | i1 >= n -> acc'
             | Map.member i1 acc' -> acc'
             | otherwise -> Map.insert
                              i1
                              (acc' Map.! i * fSquare (challenges L.!! fromIntegral j))
                              acc'


