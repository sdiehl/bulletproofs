{-# LANGUAGE TypeFamilies #-}

module Bulletproofs.Fq
  ( Fq
  , PF
  ) where

import Protolude

import PrimeField (PrimeField(..))
import Bulletproofs.Curve

-- | Prime field @Fq@ with characteristic @_q@
type Fq = PrimeField 0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141

-- | Type family to extract the characteristic of the prime field
type family PF a where
  PF (PrimeField k) = k
