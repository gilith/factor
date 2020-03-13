{- |
module: Main
description: Testing the library for factoring positive integers
license: MIT

maintainer: Joe Leslie-Hurd <joe@gilith.com>
stability: provisional
portability: portable
-}
module Main
  ( main )
where

import Test.QuickCheck

import Factor.Gaussian (Gaussian(..))
import qualified Factor.Gaussian as Gaussian

--------------------------------------------------------------------------------
-- Helper functions
--------------------------------------------------------------------------------

checkWith :: Testable prop => Args -> (String,prop) -> IO ()
checkWith args (desc,prop) = do
    putStr (desc ++ " ")
    res <- quickCheckWithResult args prop
    case res of
      Failure {} -> error "Proposition failed"
      _ -> return ()

test :: Testable prop => (String,prop) -> IO ()
test = checkWith $ stdArgs {maxSuccess = 1000}

{- No assertions yet
assert :: (String,Bool) -> IO ()
assert = checkWith $ stdArgs {maxSuccess = 1}
-}

--------------------------------------------------------------------------------
-- Generators
--------------------------------------------------------------------------------

instance Arbitrary Gaussian where
  arbitrary = do
    a <- arbitrary
    b <- arbitrary
    return (Gaussian a b)

-------------------------------------------------------------------------------
-- Testing Gaussian integers
-------------------------------------------------------------------------------

checkGaussianNormNonNegative :: Gaussian -> Bool
checkGaussianNormNonNegative x =
    n >= 0 &&
    ((n == 0) == (x == Gaussian.zero))
  where n = Gaussian.norm x

checkGaussianNormMonotonic :: Gaussian -> Gaussian -> Bool
checkGaussianNormMonotonic x y =
    y == Gaussian.zero ||
    Gaussian.norm x <= Gaussian.norm (Gaussian.multiply x y)

checkGaussianDivision :: Gaussian -> Gaussian -> Bool
checkGaussianDivision x y =
    y == Gaussian.zero ||
    ((x == Gaussian.add (Gaussian.multiply q y) r) &&
     (Gaussian.norm r <= Gaussian.norm y `div` 2))
  where (q,r) = Gaussian.division x y

checkGaussianGcd :: Gaussian -> Gaussian -> Bool
checkGaussianGcd x y =
    Gaussian.divides g x &&
    Gaussian.divides g y &&
    Gaussian.add (Gaussian.multiply s x) (Gaussian.multiply t y) == g
  where (g,(s,t)) = Gaussian.egcd x y

testGaussian :: IO ()
testGaussian = do
    test ("Gaussian integer norm is non-negative",checkGaussianNormNonNegative)
    test ("Gaussian integer norm is monotonic",checkGaussianNormMonotonic)
    test ("Gaussian integer division is correct",checkGaussianDivision)
    test ("Gaussian integer gcd is correct",checkGaussianGcd)

--------------------------------------------------------------------------------
-- Main function
--------------------------------------------------------------------------------

main :: IO ()
main = do
    testGaussian
