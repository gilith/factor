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

import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap

import Factor.Util

-------------------------------------------------------------------------------
-- Monomials in Z[x]
-------------------------------------------------------------------------------

data Monomial =
    Monomial
      {degreeMonomial :: Int,
       coeffMonomial :: Integer}
  deriving (Eq,Ord)

instance Show Monomial where
  show m = if d == 0 then show n else showCoeff ++ showPower
    where
      Monomial {degreeMonomial = d, coeffMonomial = n} = m

      showCoeff = case n of
                    1 -> ""
                    -1 -> "-"
                    _ -> show n

      showPower = "x" ++ (if d == 1 then "" else "^" ++ show d)

isZeroMonomial :: Monomial -> Bool
isZeroMonomial m = coeffMonomial m == 0

constantMonomial :: Integer -> Monomial
constantMonomial n = Monomial {degreeMonomial = 0, coeffMonomial = n}

negateMonomial :: Monomial -> Monomial
negateMonomial m = m {coeffMonomial = Prelude.negate (coeffMonomial m)}

-------------------------------------------------------------------------------
-- The polynomial ring Z[x]
-------------------------------------------------------------------------------

data Zx =
    Zx
      {degree :: Int,
       coeffMap :: IntMap Integer}
  deriving (Eq,Ord)

instance Show Zx where
  show f = case reverse (toMonomials f) of
             [] -> "0"
             m : ms -> concat (show m : map showMonomial ms)
    where
      showMonomial m | coeffMonomial m < 0 = " - " ++ show (negateMonomial m)
      showMonomial m | otherwise = " + " ++ show m

valid :: Zx -> Bool
valid f =
    all (not . isZeroMonomial) ms &&
    (if null ms then d == -1 else 0 <= head ds && d == last ds)
  where
    d = degree f
    ms = toMonomials f
    ds = map degreeMonomial ms

fromNormCoeffMap :: IntMap Integer -> Zx
fromNormCoeffMap c | IntMap.null c = zero
fromNormCoeffMap c | otherwise = Zx {degree = d, coeffMap = c}
  where (d,_) = IntMap.findMax c

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
isMonic f = not (isZero f) && powerCoeff f (degree f) == 1

powerCoeff :: Zx -> Int -> Integer
powerCoeff f i = IntMap.findWithDefault 0 i (coeffMap f)

monomials :: Zx -> [(Int,Integer)]
monomials = IntMap.toAscList . coeffMap

lengthMonomials :: Zx -> Int
lengthMonomials = IntMap.size . coeffMap

filterMonomials :: (Int -> Integer -> Bool) -> Zx -> Zx
filterMonomials p = fromNormCoeffMap . IntMap.filterWithKey p . coeffMap

constant :: Integer -> Zx
constant = monomial 0

variable :: Zx
variable = monomial 1 1

monomial :: Int -> Integer -> Zx
monomial _ 0 = zero
monomial d n = Zx {degree = d, coeffMap = IntMap.singleton d n}

simpleRoot :: Integer -> Zx
simpleRoot r = Factor.Zx.subtract variable (constant r)

evaluate :: Zx -> Integer -> Integer
evaluate f x = align 0 $ IntMap.foldrWithKey fma (0,0) $ coeffMap f
  where
    fma i n z = (i, align i z + n)
    align i (d,n) = let k = d - i in if k <= 0 then n else x^k * n

derivative :: Zx -> Zx
derivative (Zx {degree = d, coeffMap = c}) =
    if d <= 0 then zero
    else multiplyPower (-1) $ Zx {degree = d, coeffMap = deriv c}
  where
    deriv = IntMap.mapWithKey multDeg . IntMap.delete 0
    multDeg i n = toInteger i * n

fromMonomial :: Monomial -> Zx
fromMonomial (Monomial {degreeMonomial = d, coeffMonomial = n}) = monomial d n

fromMonomials :: [Monomial] -> Zx
fromMonomials = Factor.Zx.sum . map fromMonomial

toMonomials :: Zx -> [Monomial]
toMonomials = map mk . monomials
  where mk (d,n) = Monomial {degreeMonomial = d, coeffMonomial = n}

fromCoeff :: [Integer] -> Zx
fromCoeff = Factor.Zx.sum . zipWith monomial [0..]

-------------------------------------------------------------------------------
-- Ring operations
-------------------------------------------------------------------------------

zero :: Zx
zero = Zx {degree = -1, coeffMap = IntMap.empty}

one :: Zx
one = constant 1

negate :: Zx -> Zx
negate f | isZero f = zero
negate f = f {coeffMap = IntMap.map Prelude.negate (coeffMap f)}

add :: Zx -> Zx -> Zx
add f g | isZero f = g
add f g | isZero g = f
add f g | otherwise = fromNormCoeffMap c
  where
    c = IntMap.mergeWithKey addCoeff id id (coeffMap f) (coeffMap g)
    addCoeff _ fn gn = let n = fn + gn in if n == 0 then Nothing else Just n

sum :: [Zx] -> Zx
sum = foldr add zero

subtract :: Zx -> Zx -> Zx
subtract f g = add f (Factor.Zx.negate g)

multiply :: Zx -> Zx -> Zx
multiply f g | lengthMonomials g < lengthMonomials f = multiply g f
multiply f _ | isZero f = zero
multiply f g | otherwise = IntMap.foldrWithKey fma zero (coeffMap f)
  where fma i n z = add (multiplyPower i (multiplyConstant n g)) z

square :: Zx -> Zx
square f = multiply f f

product :: [Zx] -> Zx
product = foldr multiply one

multiplyConstant :: Integer -> Zx -> Zx
multiplyConstant 0 _ = zero
multiplyConstant 1 f = f
multiplyConstant n f = f {coeffMap = IntMap.map ((*) n) (coeffMap f)}

multiplyPower :: Int -> Zx -> Zx
multiplyPower 0 f = f
multiplyPower i (Zx {degree = d, coeffMap = c}) =
    if d < 0 then zero
    else Zx {degree = d + i, coeffMap = IntMap.mapKeysMonotonic ((+) i) c}

-------------------------------------------------------------------------------
-- Division
-------------------------------------------------------------------------------

division :: Zx -> Zx -> (Zx,Zx)
division f0 g = if gd < 0 then error "Zx.division by zero" else go zero f0
  where
    go q f =
        let fd = degree f in
        let d = fd - gd in
        if d < 0 then (q,f)
        else case gDiv (powerCoeff f fd) of
               Nothing -> (q,f)
               Just n -> go q' f'
                 where
                   -- f - n^d*g = q*g + r ==> f = (q + n^d)*g + r
                   q' = add q m
                   f' = Factor.Zx.subtract f (multiply m g)
                   m = monomial d n
    gd = degree g
    gDiv = multiple (powerCoeff g gd)

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
    case IntMap.minView (coeffMap f) of
      Nothing -> 1
      Just (h,t) -> IntMap.foldl gcd (abs h) t

isPrimitive :: Zx -> Bool
isPrimitive = ((==) 1) . content

primitive :: Zx -> Zx
primitive f =
    if g == 1 then f else f {coeffMap = IntMap.map gDiv (coeffMap f)}
  where
    g = content f
    gDiv = flip div g
