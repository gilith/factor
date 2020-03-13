{- |
module: Factor.Gaussian
description: Gaussian integers
license: MIT

maintainer: Joe Leslie-Hurd <joe@gilith.com>
stability: provisional
portability: portable
-}
module Factor.Gaussian
where

-------------------------------------------------------------------------------
-- A type of Gaussian integers
-------------------------------------------------------------------------------

data Gaussian = Gaussian Integer Integer
  deriving (Eq,Ord)

instance Show Gaussian where
  show x = case x of
             Gaussian a 0 -> show a
             Gaussian 0 b -> showIm b
             Gaussian a b | b < 0 -> show a ++ " - " ++ showIm (-b)
             Gaussian a b | otherwise -> show a ++ " + " ++ showIm b
    where
      showIm 1 = "i"
      showIm (-1) = "-i"
      showIm i = show i ++ "i"

-------------------------------------------------------------------------------
-- Ring operations
-------------------------------------------------------------------------------

real :: Integer -> Gaussian
real = flip Gaussian 0

imaginary :: Integer -> Gaussian
imaginary = Gaussian 0

zero :: Gaussian
zero = real 0

one :: Gaussian
one = real 1

negate :: Gaussian -> Gaussian
negate (Gaussian x y) = Gaussian (Prelude.negate x) (Prelude.negate y)

add :: Gaussian -> Gaussian -> Gaussian
add (Gaussian a b) (Gaussian c d) = Gaussian (a+c) (b+d)

subtract :: Gaussian -> Gaussian -> Gaussian
subtract x y = add x (Factor.Gaussian.negate y)

multiply :: Gaussian -> Gaussian -> Gaussian
multiply (Gaussian a b) (Gaussian c d) = Gaussian (a*c - b*d) (a*d + b*c)

-------------------------------------------------------------------------------
-- Gaussian integers form a Euclidean domain, which means there exist
-- functions
--
--   norm :: Gaussian -> Integer
--   division :: Gaussian -> Gaussian -> (Gaussian,Gaussian)
--
-- satisfying the following properties:
--
--   1. norm x >= 0
--   2. norm x == 0 <=> x == 0
--   3. y /= 0 ==> norm x <= norm (x*y)
--   4. y /= 0 && (q,r) = division x y ==> x == q*y + r && norm r < norm y
--
-- In fact the division function below satisfies the stronger property
--
--   norm r <= norm y `div` 2
-------------------------------------------------------------------------------

norm :: Gaussian -> Integer
norm (Gaussian a b) = a*a + b*b

division :: Gaussian -> Gaussian -> (Gaussian,Gaussian)
division x y = (q, Factor.Gaussian.subtract x (multiply q y))
  where
    q = Gaussian (closest (a*c + b*d)) (closest (b*c - a*d))
    closest i = (i + n2) `div` n  -- returns closest integer to i/n
    n2 = n `div` 2
    n = norm y
    Gaussian a b = x
    Gaussian c d = y

quotient :: Gaussian -> Gaussian -> Gaussian
quotient x y = fst $ division x y

remainder :: Gaussian -> Gaussian -> Gaussian
remainder x y = snd $ division x y

divides :: Gaussian -> Gaussian -> Bool
divides x y = y == zero || (x /= zero && remainder y x == zero)

-------------------------------------------------------------------------------
-- Every Euclidean domain a allows the definition of a greatest common
-- divisor function
--
--   egcd :: a -> a -> (a,(a,a))
--
-- such that if (g,(s,t)) = egcd x y then:
--
--   1. divides g x
--   2. divides g y
--   3. s*x + t*y == g
-------------------------------------------------------------------------------

egcd :: Gaussian -> Gaussian -> (Gaussian,(Gaussian,Gaussian))
egcd x y | y == zero = (x,(one,zero))
egcd x y | otherwise =
    (g, (t, Factor.Gaussian.subtract s (multiply q t)))
  where
    (q,r) = division x y
    (g,(s,t)) = egcd y r

gcd :: Gaussian -> Gaussian -> Gaussian
gcd x y = fst $ egcd x y
