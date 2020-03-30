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

import qualified Data.Set as Set

import Factor.Util

-------------------------------------------------------------------------------
-- The genuine sieve of Eratosthenes [1]
--
-- 1. https://www.cs.hmc.edu/~oneill/papers/Sieve-JFP.pdf
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

factor :: [Prime] -> Integer -> ([(Prime,Int)],Integer)
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

trialDivision :: Integer -> ([(Prime,Int)],Integer)
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

negate :: Prime -> Gfp -> Gfp
negate _ 0 = 0
negate p x = p - x

add :: Prime -> Gfp -> Gfp -> Gfp
add p x y = Factor.Prime.fromInteger p (x + y)

subtract :: Prime -> Gfp -> Gfp -> Gfp
subtract p x y = add p x (Factor.Prime.negate p y)

multiply :: Prime -> Gfp -> Gfp -> Gfp
multiply p x y = Factor.Prime.fromInteger p (x * y)

square :: Prime -> Gfp -> Gfp
square p x = multiply p x x

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

invert :: Prime -> Gfp -> Gfp
invert p x =
    if g /= 1 then error $ "Prime.invert: " ++ show x
    else if t < 0 then t + p
    else t
  where
    (g,(_,t)) = egcd p x

divide :: Prime -> Gfp -> Gfp -> Gfp
divide p x y = multiply p x (invert p y)
