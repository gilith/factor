{- |
module: Factor.Gfpx
description: The polynomial ring GF(p)[x]
license: MIT

maintainer: Joe Leslie-Hurd <joe@gilith.com>
stability: provisional
portability: portable
-}
module Factor.Gfpx
where

import qualified Data.List as List

import Factor.Prime (Gfp,Prime)
import qualified Factor.Prime as Prime
import Factor.Zx (Zx)
import qualified Factor.Zx as Zx

-------------------------------------------------------------------------------
-- The polynomial ring GF(p)[x]
-------------------------------------------------------------------------------

data Gfpx =
    Gfpx
      {degree :: Int,
       coeff :: [Gfp]}
  deriving (Ord)

instance Eq Gfpx where
  (==) f g = coeff f == coeff g

instance Show Gfpx where
  show (Gfpx {degree = d, coeff = c}) =
      show (Zx.Zx {Zx.degree = d, Zx.coeff = c})

valid :: Prime -> Gfpx -> Bool
valid p f =
    all (Prime.valid p) c &&
    normCoeff c == c &&
    degree f == length c - 1
  where
    c = coeff f

normCoeff :: [Gfp] -> [Gfp]
normCoeff = List.dropWhileEnd ((==) 0)

fromNormCoeff :: [Gfp] -> Gfpx
fromNormCoeff c = Gfpx {degree = length c - 1, coeff = c}

fromCoeff :: [Gfp] -> Gfpx
fromCoeff = fromNormCoeff . normCoeff

fromZx :: Prime -> Zx -> Gfpx
fromZx p = fromCoeff . map (Prime.fromInteger p) . Zx.coeff

-------------------------------------------------------------------------------
-- Polynomial operations
-------------------------------------------------------------------------------

isZero :: Gfpx -> Bool
isZero f = degree f < 0

isConstant :: Gfpx -> Bool
isConstant f = degree f <= 0

isLinear :: Gfpx -> Bool
isLinear f = degree f <= 1

isMonic :: Gfpx -> Bool
isMonic f = not (isZero f) && last (coeff f) == 1

constantCoeff :: Gfpx -> Gfp
constantCoeff f = case coeff f of {c : _ -> c; _ -> 0}

linearCoeff :: Gfpx -> Gfp
linearCoeff f = case coeff f of {_ : c : _ -> c; _ -> 0}

constant :: Gfp -> Gfpx
constant x = fromCoeff [x]

monomial :: Gfp -> Int -> Gfpx
monomial x d = multiplyPower d $ constant x

evaluate :: Prime -> Gfpx -> Gfp -> Gfp
evaluate p f x = foldr fma 0 (coeff f)
  where fma c z = Prime.add p (Prime.multiply p z x) c

-------------------------------------------------------------------------------
-- Ring operations
-------------------------------------------------------------------------------

zero :: Gfpx
zero = Factor.Gfpx.constant 0

one :: Gfpx
one = Factor.Gfpx.constant 1

negate :: Prime -> Gfpx -> Gfpx
negate p f = f {coeff = map (Prime.negate p) (coeff f)}

add :: Prime -> Gfpx -> Gfpx -> Gfpx
add p f g =
    case compare fd gd of
      LT -> g {coeff = zipWith (Prime.add p) fc gc ++ drop (fd + 1) gc}
      EQ -> fromCoeff (zipWith (Prime.add p) fc gc)
      GT -> f {coeff = zipWith (Prime.add p) fc gc ++ drop (gd + 1) fc}
  where
    Gfpx {degree = fd, coeff = fc} = f
    Gfpx {degree = gd, coeff = gc} = g

subtract :: Prime -> Gfpx -> Gfpx -> Gfpx
subtract p f g = add p f (Factor.Gfpx.negate p g)

multiply :: Prime -> Gfpx -> Gfpx -> Gfpx
multiply p f g =
    if fd < 0 || gd < 0 then zero
    else Gfpx {degree = fd + gd, coeff = go [] fc}
  where
    go acc [] = acc
    go acc (fch : fct) = s : go acc' fct
      where (s,acc') = advance $ update acc fch

    advance [] = (0,[])
    advance (s : acc) = (s,acc)

    update acc 0 = acc
    update acc fch = fma acc fch gc

    fma [] y zs = map (Prime.multiply p y) zs
    fma xs _ [] = xs
    fma (x : xs) y (z : zs) = Prime.add p x (Prime.multiply p y z) : fma xs y zs

    Gfpx {degree = fd, coeff = fc} = f
    Gfpx {degree = gd, coeff = gc} = g

multiplyConstant :: Prime -> Gfp -> Gfpx -> Gfpx
multiplyConstant _ 0 _ = zero
multiplyConstant _ 1 f = f
multiplyConstant p x f = multiply p (constant x) f

multiplyPower :: Int -> Gfpx -> Gfpx
multiplyPower d f =
    if d == 0 || fd < 0 then f
    else Gfpx {degree = fd + d, coeff = replicate d 0 ++ fc}
  where
    Gfpx {degree = fd, coeff = fc} = f

multiplyMonomial :: Prime -> Gfp -> Int -> Gfpx -> Gfpx
multiplyMonomial p x d f = multiplyPower d $ multiplyConstant p x f

-------------------------------------------------------------------------------
-- Division
-------------------------------------------------------------------------------

division :: Prime -> Gfpx -> Gfpx -> (Gfpx,Gfpx)
division p f0 g = if gd < 0 then error "Gfpx.division by zero" else go zero f0
  where
    go q f = if d < 0 then (q,f) else go q' f'
      where
        d = degree f - gd
        x = Prime.multiply p (last (coeff f)) gx
        -- f - x^d*g = q*g + r ==> f = (q + x^d)*g + r
        q' = add p q (monomial x d)
        f' = Factor.Gfpx.subtract p f (multiplyMonomial p x d g)
    gd = degree g
    gx = Prime.invert p (last (coeff g))

quotient :: Prime -> Gfpx -> Gfpx -> Gfpx
quotient p f g = fst $ Factor.Gfpx.division p f g

remainder :: Prime -> Gfpx -> Gfpx -> Gfpx
remainder p f g = snd $ Factor.Gfpx.division p f g

divides :: Prime -> Gfpx -> Gfpx -> Bool
divides p f g = isZero g || (not (isZero f) && isZero (remainder p g f))

-------------------------------------------------------------------------------
-- Every Euclidean domain a admits the definition of a greatest common
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

egcd :: Prime -> Gfpx -> Gfpx -> (Gfpx,(Gfpx,Gfpx))
egcd p = go
  where
    go f g | isZero g =
        if isZero f then (zero,(zero,zero)) else (h, (constant x, zero))
      where
        x = Prime.invert p (last (coeff f))
        h = multiplyConstant p x f
    go f g | otherwise =
        (h, (t, Factor.Gfpx.subtract p s (multiply p q t)))
      where
        (q,r) = division p f g
        (h,(s,t)) = go g r

gcd :: Prime -> Gfpx -> Gfpx -> Gfpx
gcd p x y = fst $ egcd p x y

-------------------------------------------------------------------------------
-- Polynomial composition
-------------------------------------------------------------------------------

compose :: Prime -> Gfpx -> Gfpx -> Gfpx
compose p f g = foldr fma zero (coeff f)
  where fma c z = add p (constant c) (multiply p z g)

-------------------------------------------------------------------------------
-- Finding all roots of a polynomial f [1, sec 4.2]
--
-- 1. Matthew Briggs, An Introduction to the General Number Field Sieve
-------------------------------------------------------------------------------

roots :: Prime -> Gfpx -> [Gfp]
roots p | p < 3 = \f -> filter (\x -> evaluate p f x == 0) [0..(p-1)]
roots p | otherwise =
    \f -> if isLinear f then lin (coeff f)
          else List.sort (go (Factor.Gfpx.gcd p xp f))
  where
    go f | isLinear f = lin (coeff f)
    go f | constantCoeff f == 0 = 0 : go (fromNormCoeff (tail (coeff f)))
    go f | otherwise =
        if 0 < d1 && d1 < degree f then go f1 ++ go f2
        else map (Prime.add p 1) (go (compose p f x1))
      where
        d1 = degree f1
        f1 = Factor.Gfpx.gcd p f xp1
        f2 = quotient p f f1

    lin [] = [0..(p-1)]
    lin [_] = []
    lin [b,a] = [Prime.divide p (Prime.negate p b) a]  -- ax + b = 0
    lin _ = error "Gfpx.roots.lin: not a linear polynomial"

    -- x^p - x == product [ (x - i) | 0 <= i < p ]
    xp = fromNormCoeff (0 : (p-1) : replicate (fromInteger p - 2) 0 ++ [1])

    -- x^p - x == x * (x^((p-1)/2) + 1) * (x^((p-1)/2) - 1)
    xp1 = fromNormCoeff (1 : replicate (fromInteger (p `div` 2) - 1) 0 ++ [1])

    -- x + 1
    x1 = fromNormCoeff [1,1]
