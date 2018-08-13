{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveGeneric #-}

module Bulletproofs.Fq where

import Protolude

import Crypto.Random (MonadRandom)
import Crypto.Number.Generate (generateMax)

import Bulletproofs.Curve

-------------------------------------------------------------------------------
-- Types
-------------------------------------------------------------------------------

-- | Prime field with characteristic @_q@
newtype Fq = Fq Integer -- ^ Use @new@ instead of this constructor
  deriving (Show, Eq, Bits, Ord, Generic, NFData)

instance Num Fq where
  (+)           = fqAdd
  (*)           = fqMul
  abs           = panic "There is no absolute value in a finite field"
  signum        = panic "This function doesn't make sense in a finite field"
  negate        = fqNeg
  fromInteger   = new

instance Fractional Fq where
  (/) = fqDiv
  fromRational (a :% b) = Fq a / Fq b

-- | Turn an integer into an @Fq@ number, should be used instead of
-- the @Fq@ constructor.
new :: Integer -> Fq
new a = Fq (a `mod` q)

{-# INLINE norm #-}
norm :: Fq -> Fq
norm (Fq a) = Fq (a `mod` q)

{-# INLINE fqAdd #-}
fqAdd :: Fq -> Fq -> Fq
fqAdd (Fq a) (Fq b) = norm (Fq (a+b))

{-# INLINE fqMul #-}
fqMul :: Fq -> Fq -> Fq
fqMul (Fq a) (Fq b) = norm (Fq (a*b))

{-# INLINE fqNeg #-}
fqNeg :: Fq -> Fq
fqNeg (Fq a) = Fq ((-a) `mod` q)

{-# INLINE fqDiv #-}
fqDiv :: Fq -> Fq -> Fq
fqDiv a b = fqMul a (inv b)

{-# INLINE fqInv #-}
-- | Multiplicative inverse
fqInv :: Fq -> Fq
fqInv x = 1 / x

{-# INLINE fqZero #-}
-- | Additive identity
fqZero :: Fq
fqZero = Fq 0

{-# INLINE fqOne #-}
-- | Multiplicative identity
fqOne :: Fq
fqOne = Fq 1

fqSquare :: Fq -> Fq
fqSquare x = fqMul x x

fqCube :: Fq -> Fq
fqCube x = fqMul x (fqMul x x)

fqPower :: Fq -> Integer -> Fq
fqPower base exp = fqPower' base exp (Fq 1)

fqPower' :: Fq  -> Integer -> Fq -> Fq
fqPower' base 0 acc = acc
fqPower' base exp acc = fqPower' base (exp - 1) (fqMul base acc)

inv :: Fq -> Fq
inv (Fq a) = Fq $ euclidean a q `mod` q

asInteger :: Fq -> Integer
asInteger (Fq n) = n

-- | Euclidean algorithm to compute inverse in an integral domain @a@
euclidean :: (Integral a) => a -> a -> a
euclidean a b = fst (inv' a b)

{-# INLINEABLE inv' #-}
{-# SPECIALISE inv' :: Integer -> Integer -> (Integer, Integer) #-}
inv' :: (Integral a) => a -> a -> (a, a)
inv' a b =
  case b of
   1 -> (0, 1)
   _ -> let (e, f) = inv' b d
        in (f, e - c*f)
  where c = a `div` b
        d = a `mod` b

random :: MonadRandom m => m Fq
random = Fq <$> generateMax q


