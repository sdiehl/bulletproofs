module Bulletproofs.InnerProductProof.Internal where

import Protolude

import qualified Crypto.PubKey.ECC.Types as Crypto
import Bulletproofs.Fq

data InnerProductProof
  = InnerProductProof
    { lCommits :: [Crypto.Point]
    -- ^ Vector of commitments of the elements in the original vector l
    -- whose size is the logarithm of base 2 of the size of vector l
    , rCommits :: [Crypto.Point]
    -- ^ Vector of commitments of the elements in the original vector r
    -- whose size is the logarithm of base 2 of the size of vector r
    , l :: Fq
    -- ^ Remaining element of vector l at the end of
    -- the recursive algorithm that generates the inner-product proof
    , r :: Fq
    -- ^ Remaining element of vector r at the end of
    -- the recursive algorithm that generates the inner-product proof
    } deriving (Show, Eq)

data InnerProductWitness
  = InnerProductWitness
    { ls :: [Fq]
    -- ^ Vector of values l that the prover uses to compute lCommits
    -- in the recursive inner product algorithm
    , rs :: [Fq]
    -- ^ Vector of values r that the prover uses to compute rCommits
    -- in the recursive inner product algorithm
    } deriving (Show, Eq)

data InnerProductBase
  = InnerProductBase
    { bGs :: [Crypto.Point]  -- ^ Independent generator Gs ∈ G^n
    , bHs :: [Crypto.Point]  -- ^ Independent generator Hs ∈ G^n
    , bH :: Crypto.Point
    -- ^ Internally fixed group element H ∈  G
    -- for which there is no known discrete-log relation among Gs, Hs, bG
    } deriving (Show, Eq)

