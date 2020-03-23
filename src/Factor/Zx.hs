{- |
module: Factor.Zx
description: The polynomial ring Z[x]
license: MIT

maintainer: Joe Leslie-Hurd <joe@gilith.com>
stability: provisional
portability: portable
-}
module Factor.Zx
where

import qualified Data.List as List

import Factor.Util

-------------------------------------------------------------------------------
-- The polynomial ring Z[x]
-------------------------------------------------------------------------------

data Zx =
    Zx
      {degree :: Int,
       coeff :: [Integer]}
  deriving (Ord)

instance Eq Zx where
  (==) f g = coeff f == coeff g

instance Show Zx where
  show f = case reverse (coeff f) of
             [] -> "0"
             n : c -> let (d,l) = foldr showCoeff (0,[]) c in
                      concat (showMonomial n d ++ l)
    where
      showCoeff n (d,l) = (d + 1, showLaterMonomial n d ++ l)

      showLaterMonomial 0 _ = []
      showLaterMonomial n d | n < 0 = " - " : showMonomial (-n) d
      showLaterMonomial n d | otherwise = " + " : showMonomial n d

      showMonomial n 0 = [show n]
      showMonomial n d = showPowerCoeff n ++ showPower d

      showPowerCoeff 1 = []
      showPowerCoeff (-1) = ["-"]
      showPowerCoeff n = [show n]

      showPower :: Int -> [String]
      showPower d = "x" : (if d == 1 then [] else ["^", show d])

valid :: Zx -> Bool
valid f =
    normCoeff c == c &&
    degree f == length c - 1
  where
    c = coeff f

normCoeff :: [Integer] -> [Integer]
normCoeff = List.dropWhileEnd ((==) 0)

fromNormCoeff :: [Integer] -> Zx
fromNormCoeff c = Zx {degree = length c - 1, coeff = c}

fromCoeff :: [Integer] -> Zx
fromCoeff = fromNormCoeff . normCoeff

-------------------------------------------------------------------------------
-- Polynomial operations
-------------------------------------------------------------------------------

isZero :: Zx -> Bool
isZero f = degree f < 0

isConstant :: Zx -> Bool
isConstant f = degree f <= 0

isLinear :: Zx -> Bool
isLinear f = degree f <= 1

isMonic :: Zx -> Bool
isMonic f = not (isZero f) && last (coeff f) == 1

constant :: Integer -> Zx
constant n = fromCoeff [n]

monomial :: Integer -> Int -> Zx
monomial n d = multiplyPower d $ constant n

evaluate :: Zx -> Integer -> Integer
evaluate f x = foldr fma 0 (coeff f)
  where fma c z = z*x + c

-------------------------------------------------------------------------------
-- Ring operations
-------------------------------------------------------------------------------

zero :: Zx
zero = Factor.Zx.constant 0

one :: Zx
one = Factor.Zx.constant 1

negate :: Zx -> Zx
negate f = f {coeff = map Prelude.negate (coeff f)}

add :: Zx -> Zx -> Zx
add f g =
    case compare fd gd of
      LT -> g {coeff = zipWith (+) fc gc ++ drop (fd + 1) gc}
      EQ -> fromCoeff (zipWith (+) fc gc)
      GT -> f {coeff = zipWith (+) fc gc ++ drop (gd + 1) fc}
  where
    Zx {degree = fd, coeff = fc} = f
    Zx {degree = gd, coeff = gc} = g

subtract :: Zx -> Zx -> Zx
subtract f g = add f (Factor.Zx.negate g)

multiply :: Zx -> Zx -> Zx
multiply f g =
    if fd < 0 || gd < 0 then zero
    else Zx {degree = fd + gd, coeff = go [] fc}
  where
    go acc [] = acc
    go acc (fch : fct) = s : go acc' fct
      where (s,acc') = advance $ update acc fch

    advance [] = (0,[])
    advance (s : acc) = (s,acc)

    update acc 0 = acc
    update acc fch = fma acc fch gc

    fma [] y zs = map ((*) y) zs
    fma xs _ [] = xs
    fma (x : xs) y (z : zs) = (x + y*z) : fma xs y zs

    Zx {degree = fd, coeff = fc} = f
    Zx {degree = gd, coeff = gc} = g

multiplyConstant :: Integer -> Zx -> Zx
multiplyConstant 0 _ = zero
multiplyConstant 1 f = f
multiplyConstant n f = multiply (constant n) f

multiplyPower :: Int -> Zx -> Zx
multiplyPower d f =
    if d == 0 || fd < 0 then f
    else Zx {degree = fd + d, coeff = replicate d 0 ++ fc}
  where
    Zx {degree = fd, coeff = fc} = f

multiplyMonomial :: Integer -> Int -> Zx -> Zx
multiplyMonomial n d f = multiplyPower d $ multiplyConstant n f

-------------------------------------------------------------------------------
-- Division
-------------------------------------------------------------------------------

division :: Zx -> Zx -> (Zx,Zx)
division f0 g = if gd < 0 then error "Zx.division by zero" else go zero f0
  where
    go q f =
        let d = degree f - gd in
        if d < 0 then (q,f)
        else case gDiv (last (coeff f)) of
               Nothing -> (q,f)
               Just n -> go q' f'
                 where
                   -- f - n^d*g = q*g + r ==> f = (q + n^d)*g + r
                   q' = add q (monomial n d)
                   f' = Factor.Zx.subtract f (multiplyMonomial n d g)
    gd = degree g
    gDiv = multiple (last (coeff g))

quotient :: Zx -> Zx -> Zx
quotient f g = fst $ Factor.Zx.division f g

remainder :: Zx -> Zx -> Zx
remainder f g = snd $ Factor.Zx.division f g

divides :: Zx -> Zx -> Bool
divides f g = isZero g || (not (isZero f) && isZero (remainder g f))

-------------------------------------------------------------------------------
-- Primitive part and content [1]
--
-- 1. https://en.wikipedia.org/wiki/Primitive_part_and_content
-------------------------------------------------------------------------------

content :: Zx -> Integer
content f =
    case coeff f of
      [] -> 1
      h : t -> go (abs h) t
  where
    go 1 _ = 1
    go c [] = c
    go c (h : t) = go (gcd c h) t

isPrimitive :: Zx -> Bool
isPrimitive = ((==) 1) . content

primitive :: Zx -> Zx
primitive f = if g == 1 then f else f {coeff = map gDiv (coeff f)}
  where
    g = content f
    gDiv = flip div g
