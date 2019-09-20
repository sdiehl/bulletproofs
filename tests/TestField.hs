{-# LANGUAGE ScopedTypeVariables #-}

module TestField where

import Protolude

import Test.Tasty
import Test.Tasty.QuickCheck

import Data.Curve.Weierstrass.SECP256K1 (Fr, PA)
import Data.Curve.Weierstrass

import TestCommon

prop_addMod :: Fr -> Fr -> Property
prop_addMod x y
  = left === right
  where
    left :: PA
    left = gen `mul` (x + y)

    right :: PA
    right = (gen `mul` x) `add` (gen `mul` y)

prop_subMod :: Fr -> Fr -> Property
prop_subMod x y
  = left === right
  where
    left :: PA
    left = gen `mul` (x - y)

    right :: PA
    right = (gen `mul` x) `add` inv (gen `mul` y)

-------------------------------------------------------------------------------
-- Laws of field operations
-------------------------------------------------------------------------------

testFieldLaws
  :: forall a . (Fractional a, Eq a, Arbitrary a, Show a)
  => Proxy a
  -> TestName
  -> TestTree
testFieldLaws _ descr
  = testGroup ("Test field laws of " <> descr)
    [ testProperty "commutativity of addition"
      $ commutes ((+) :: a -> a -> a)
    , testProperty "commutativity of multiplication"
      $ commutes ((*) :: a -> a -> a)
    , testProperty "associavity of addition"
      $ associates ((+) :: a -> a -> a)
    , testProperty "associavity of multiplication"
      $ associates ((*) :: a -> a -> a)
    , testProperty "additive identity"
      $ isIdentity ((+) :: a -> a -> a) 0
    , testProperty "multiplicative identity"
      $ isIdentity ((*) :: a -> a -> a) 1
    , testProperty "additive inverse"
      $ isInverse ((+) :: a -> a -> a) negate 0
    , testProperty "multiplicative inverse"
      $ \x -> (x /= (0 :: a)) ==> isInverse ((*) :: a -> a -> a) recip 1 x
    , testProperty "multiplication distributes over addition"
      $ distributes ((*) :: a -> a -> a) (+)
    ]

-------------------------------------------------------------------------------
-- Fq
-------------------------------------------------------------------------------

test_fieldLaws_Fq :: TestTree
test_fieldLaws_Fq = testFieldLaws (Proxy :: Proxy Fr) "Fr"
