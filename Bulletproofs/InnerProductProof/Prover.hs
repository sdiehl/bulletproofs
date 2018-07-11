{-# LANGUAGE NamedFieldPuns, MultiWayIf #-}

module Bulletproofs.InnerProductProof.Prover ( 
  generateProof,
) where

import Protolude

import qualified Data.List as L
import qualified Data.Map as Map

import qualified Crypto.PubKey.ECC.Types as Crypto

import Bulletproofs.Curve
import Bulletproofs.Utils
import Bulletproofs.Fq as Fq

import Bulletproofs.InnerProductProof.Internal

-- | Generate proof that a witness l, r satisfies the inner product relation
-- on public input (Gs, Hs, h)
generateProof
  :: InnerProductBase    -- ^ Generators Gs, Hs, h
  -> Crypto.Point
  -- ^ Commitment P = A + xS − zG + (z*y^n + z^2 * 2^n) * hs' of vectors l and r
  -- whose inner product is t
  -> InnerProductWitness
  -- ^ Vectors l and r that hide bit vectors aL and aR, respectively
  -> InnerProductProof
generateProof productBase commitmentLR witness
  = generateProof' productBase commitmentLR witness [] []

generateProof'
  :: InnerProductBase
  -> Crypto.Point
  -> InnerProductWitness
  -> [Crypto.Point]
  -> [Crypto.Point]
  -> InnerProductProof
generateProof'
  InnerProductBase{ bGs, bHs, bH }
  commitmentLR
  InnerProductWitness{ ls, rs }
  lCommits
  rCommits
  = case (ls, rs) of
    ([l], [r]) -> InnerProductProof (reverse lCommits) (reverse rCommits) l r
    _          -> if | not checkLGs -> panic "Error in: l' * Gs' == l * Gs + x^2 * A_L + x^(-2) * A_R"
                     | not checkRHs -> panic "Error in: r' * Hs' == r * Hs + x^2 * B_L + x^(-2) * B_R"
                     | not checkLBs -> panic "Error in: l' * r' == l * r + x^2 * (lsLeft * rsRight) + x^-2 * (lsRight * rsLeft)"
                     | not checkC -> panic "Error in: C == zG + aG + bH'"
                     | not checkC' -> panic "Error in: C' = C + x^2 L + x^-2 R == z'G + a'G + b'H'"
                     | otherwise -> generateProof'
                         InnerProductBase { bGs = gs'', bHs = hs'', bH = bH }
                         commitmentLR'
                         InnerProductWitness { ls = ls', rs = rs' }
                         (lCommit:lCommits)
                         (rCommit:rCommits)
  where
    n' = fromIntegral $ length ls
    nPrime = n' `div` 2

    (lsLeft, lsRight) = splitAt nPrime ls
    (rsLeft, rsRight) = splitAt nPrime rs
    (gsLeft, gsRight) = splitAt nPrime bGs
    (hsLeft, hsRight) = splitAt nPrime bHs

    cL = dotp lsLeft rsRight
    cR = dotp lsRight rsLeft

    lCommit = foldl' addP Crypto.PointO (zipWith mulP lsLeft gsRight)
         `addP`
         foldl' addP Crypto.PointO (zipWith mulP rsRight hsLeft)
         `addP`
         (cL `mulP` bH)

    rCommit = foldl' addP Crypto.PointO (zipWith mulP lsRight gsLeft)
         `addP`
         foldl' addP Crypto.PointO (zipWith mulP rsLeft hsRight)
         `addP`
         (cR `mulP` bH)

    x = shamirX' commitmentLR lCommit rCommit

    xInv = inv x
    xs = replicate nPrime x
    xsInv = replicate nPrime xInv

    gs'' = zipWith addP (zipWith mulP xsInv gsLeft) (zipWith mulP xs gsRight)
    hs'' = zipWith addP (zipWith mulP xs hsLeft) (zipWith mulP xsInv hsRight)

    ls' = ((*) x <$> lsLeft) `fqAddV` ((*) xInv <$> lsRight)
    rs' = ((*) xInv <$> rsLeft) `fqAddV` ((*) x <$> rsRight)

    commitmentLR'
      = (fqSquare x `mulP` lCommit)
        `addP`
        (fqSquare xInv `mulP` rCommit)
        `addP`
        commitmentLR

    -----------------------------
    -- Checks
    -----------------------------

    aL' = foldl' addP Crypto.PointO (zipWith mulP lsLeft gsRight)
    aR' = foldl' addP Crypto.PointO (zipWith mulP lsRight gsLeft)

    bL' = foldl' addP Crypto.PointO (zipWith mulP rsLeft hsRight)
    bR' = foldl' addP Crypto.PointO (zipWith mulP rsRight hsLeft)

    z = dotp ls rs
    z' = dotp ls' rs'

    lGs = foldl' addP Crypto.PointO (zipWith mulP ls bGs)
    rHs = foldl' addP Crypto.PointO (zipWith mulP rs bHs)

    lGs' = foldl' addP Crypto.PointO (zipWith mulP ls' gs'')
    rHs' = foldl' addP Crypto.PointO (zipWith mulP rs' hs'')

    checkLGs
      = lGs'
        ==
        foldl' addP Crypto.PointO (zipWith mulP ls bGs)
        `addP`
        (fqSquare x `mulP` aL')
        `addP`
        (fqSquare xInv `mulP` aR')

    checkRHs
      = rHs'
        ==
        foldl' addP Crypto.PointO (zipWith mulP rs bHs)
        `addP`
        (fqSquare x `mulP` bR')
        `addP`
        (fqSquare xInv `mulP` bL')

    checkLBs
      = dotp ls' rs'
        ==
        dotp ls rs + fqSquare x * cL + fqSquare xInv * cR

    checkC
      = commitmentLR
        ==
        (z `mulP` bH)
        `addP`
        lGs
        `addP`
        rHs

    checkC'
      = commitmentLR'
        ==
        (z' `mulP` bH)
        `addP`
        lGs'
        `addP`
        rHs'


