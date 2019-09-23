{-# LANGUAGE DeriveAnyClass, DeriveGeneric #-}
module Bulletproofs.InnerProductProof.Internal (
  InnerProductProof(..),
  InnerProductWitness(..),
  InnerProductBase(..),
) where

import Protolude

data InnerProductProof f p
  = InnerProductProof
    { lCommits :: [p]
    -- ^ Vector of commitments of the elements in the original vector l
    -- whose size is the logarithm of base 2 of the size of vector l
    , rCommits :: [p]
    -- ^ Vector of commitments of the elements in the original vector r
    -- whose size is the logarithm of base 2 of the size of vector r
    , l :: f
    -- ^ Remaining element of vector l at the end of
    -- the recursive algorithm that generates the inner-product proof
    , r :: f
    -- ^ Remaining element of vector r at the end of
    -- the recursive algorithm that generates the inner-product proof
    } deriving (Show, Eq, Generic, NFData)

data InnerProductWitness f
  = InnerProductWitness
    { ls :: [f]
    -- ^ Vector of values l that the prover uses to compute lCommits
    -- in the recursive inner product algorithm
    , rs :: [f]
    -- ^ Vector of values r that the prover uses to compute rCommits
    -- in the recursive inner product algorithm
    } deriving (Show, Eq)

data InnerProductBase p
  = InnerProductBase
    { bGs :: [p]  -- ^ Independent generator Gs ∈ G^n
    , bHs :: [p]  -- ^ Independent generator Hs ∈ G^n
    , bH :: p
    -- ^ Internally fixed group element H ∈  G
    -- for which there is no known discrete-log relation among Gs, Hs, bG
    } deriving (Show, Eq)

