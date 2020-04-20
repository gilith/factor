{- |
module: Factor.Prime
description: Prime integers
license: MIT

maintainer: Joe Leslie-Hurd <joe@gilith.com>
stability: provisional
portability: portable
-}

module Factor.Prime
where

import qualified Data.List as List
import qualified Data.Set as Set

import Factor.Util

-------------------------------------------------------------------------------
-- The genuine sieve of Eratosthenes
--
-- https://www.cs.hmc.edu/~oneill/papers/Sieve-JFP.pdf
-------------------------------------------------------------------------------

type Prime = Integer

list :: [Prime]
list = 2 : 3 : sieve 5 ((9,6),Set.empty)
  where
    sieve n ((kp,p),s) =
      case compare n kp of
        LT -> n : sieve (n+2) ((kp,p), Set.insert (n*n,2*n) s)
        EQ -> sieve (n+2) (next kp p s)
        GT -> sieve n (next kp p s)

    next kp p s = Set.deleteFindMin (Set.insert (kp + p, p) s)

-------------------------------------------------------------------------------
-- Trial division
-------------------------------------------------------------------------------

type PrimePower = (Prime,Int)

multiplyPrimePowers :: [PrimePower] -> [PrimePower] -> [PrimePower]
multiplyPrimePowers pks1 [] = pks1
multiplyPrimePowers [] pks2 = pks2
multiplyPrimePowers ((p1,k1) : pks1) ((p2,k2) : pks2) =
    case compare p1 p2 of
      LT -> (p1,k1) : multiplyPrimePowers pks1 ((p2,k2) : pks2)
      EQ -> (p1, k1 + k2) : multiplyPrimePowers pks1 pks2
      GT -> (p2,k2) : multiplyPrimePowers ((p1,k1) : pks1) pks2

productPrimePowers :: [[PrimePower]] -> [PrimePower]
productPrimePowers [] = []
productPrimePowers [pks] = pks
productPrimePowers pksl = multiplyPrimePowers pks1 pks2
  where
    pks1 = productPrimePowers pksl1
    pks2 = productPrimePowers pksl2
    (pksl1,pksl2) = List.splitAt (length pksl `div` 2) pksl

factor :: [Prime] -> Integer -> ([PrimePower],Integer)
factor _ 0 = ([],0)
factor ps n | n < 0 = (pks, Prelude.negate s)
  where (pks,s) = factor ps (Prelude.negate n)
factor ps0 n0 | otherwise = go ps0 n0
  where
    go _ 1 = ([],1)
    go [] n = ([],n)
    go (p : ps) n = (if k == 0 then pks else (p,k) : pks, s)
      where
        (pks,s) = go ps m
        (k,m) = divPower p n

factorProduct :: [Prime] -> [Integer] -> ([PrimePower],[Integer])
factorProduct ps nl = (productPrimePowers pksl, sl)
  where (pksl,sl) = unzip $ map (factor ps) nl

trialDivision :: Integer -> ([PrimePower],Integer)
trialDivision = factor list

-------------------------------------------------------------------------------
-- The field GF(p) of arithmetic modulo a prime
-------------------------------------------------------------------------------

type Gfp = Integer

valid :: Prime -> Gfp -> Bool
valid p x = 0 <= x && x < p

fromInt :: Prime -> Int -> Gfp
fromInt p = Factor.Prime.fromInteger p . toInteger

fromInteger :: Prime -> Integer -> Gfp
fromInteger p n = n `mod` p

toSmallestInteger :: Prime -> Gfp -> Integer
toSmallestInteger p x = if p - x < x then x - p else x

negate :: Prime -> Gfp -> Gfp
negate _ 0 = 0
negate p x = p - x

add :: Prime -> Gfp -> Gfp -> Gfp
add p x y = Factor.Prime.fromInteger p (x + y)

sum :: Prime -> [Gfp] -> Gfp
sum p = foldr (add p) 0

subtract :: Prime -> Gfp -> Gfp -> Gfp
subtract p x y = add p x (Factor.Prime.negate p y)

multiply :: Prime -> Gfp -> Gfp -> Gfp
multiply p x y = Factor.Prime.fromInteger p (x * y)

square :: Prime -> Gfp -> Gfp
square p x = multiply p x x

product :: Prime -> [Gfp] -> Gfp
product p = foldr (multiply p) 1

multiplyExp :: Prime -> Gfp -> Gfp -> Integer -> Gfp
multiplyExp _ 0 _ _ = 0
multiplyExp _ z _ 0 = z
multiplyExp _ _ 0 _ = 0
multiplyExp p z0 x0 k0 = go z0 x0 k0
  where
    go z _ 0 = z
    go z 1 _ = z
    go z x k = go z' x' k'
      where
        z' = if even k then z else multiply p z x
        x' = square p x
        k' = k `div` 2

exp :: Prime -> Gfp -> Integer -> Gfp
exp p = multiplyExp p 1

exp2 :: Prime -> Gfp -> Int -> Gfp
exp2 _ x 0 = x
exp2 p x k = exp2 p (square p x) (k - 1)

invert :: Prime -> Gfp -> Gfp
invert p x =
    if g /= 1 then error $ "Prime.invert: " ++ show x
    else if t < 0 then t + p
    else t
  where
    (g,(_,t)) = egcd p x

divide :: Prime -> Gfp -> Gfp -> Gfp
divide p x y = multiply p x (invert p y)

-------------------------------------------------------------------------------
-- Square roots in GF(p) using the Tonelli-Shanks algorithm
-------------------------------------------------------------------------------

isResidue :: Prime -> Integer -> Bool
isResidue p n = jacobiSymbol n p == Residue

nonResidue :: Prime -> Integer -> Bool
nonResidue p n = jacobiSymbol n p == NonResidue

nextResidue :: Prime -> Integer -> Integer
nextResidue p n = if isResidue p n then n else nextResidue p (n + 1)

nextNonResidue :: Prime -> Integer -> Integer
nextNonResidue 2 _ = error "no non-residues modulo 2"
nextNonResidue p n = if nonResidue p n then n else nextNonResidue p (n + 1)

sqrt :: Prime -> Gfp -> Gfp
sqrt 2 = id
sqrt p =
    if r == 1 then sqrt3Mod4
    else if r == 2 then sqrt5Mod8
    else tonelliShanks
  where
    (r,s) = divPower 2 (p - 1)

    sqrt3Mod4 x = Factor.Prime.exp p x sqrt3Mod4Exp

    sqrt3Mod4Exp = (p + 1) `div` 4

    sqrt5Mod8 x = Factor.Prime.product p [x, y, z - 1]
      where
        x2 = multiply p 2 x
        y = Factor.Prime.exp p x2 sqrt5Mod8Exp
        z = multiply p x2 (square p y)

    sqrt5Mod8Exp = (p - 5) `div` 8

    tonelliShanks x =
        if isResidue p x then tonelliShanksLoop tonelliShanksInit d t r else 0
      where
        d = Factor.Prime.exp p x ((s + 1) `div` 2)
        t = Factor.Prime.exp p x s

    tonelliShanksInit = Factor.Prime.exp p (nextNonResidue p 2) s

    tonelliShanksLoop c d t m =
        if t == 1 then d else tonelliShanksLoop b2 db tb2 i
      where
        i = tonelliShanksMin t 1
        b = exp2 p c (m - (i + 1))
        b2 = square p b
        db = multiply p d b
        tb2 = multiply p t b2

    tonelliShanksMin t i =
        if t2 == 1 then i else tonelliShanksMin t2 (i + 1)
      where
        t2 = square p t
