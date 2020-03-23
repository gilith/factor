{- |
module: Factor.Nfs
description: The general number field sieve
license: MIT

maintainer: Joe Leslie-Hurd <joe@gilith.com>
stability: provisional
portability: portable
-}
module Factor.Nfs
where

import qualified Factor.Gfpx as Gfpx
import Factor.Prime (Gfp,Prime)
import qualified Factor.Prime as Prime
import Factor.Util
import Factor.Zx (Zx)
import qualified Factor.Zx as Zx

-------------------------------------------------------------------------------
-- Polynomial selection
--
-- Given n, return m and f such that f is monic and f(m) == n
-------------------------------------------------------------------------------

selectDegree :: Integer -> Int
selectDegree = const 4

selectPolynomialBase :: Bool -> Int -> Integer -> (Integer,Zx)
selectPolynomialBase pos d n = (m, Zx.fromCoeff (x : c))
  where
    (x,c) = foldr reduce (n - last ms, [1]) (init ms)

    reduce mi (t,l) = (r, q : l)
      where (q,r) = idiv t mi

    ms = take d $ iterate ((*) m) m
    m = root d n

    root = if pos then nthRoot else nthRootClosest
    idiv = if pos then division else divisionClosest

selectPolynomial :: Integer -> (Integer,Zx)
selectPolynomial n = selectPolynomialBase False d n
  where d = selectDegree n

-------------------------------------------------------------------------------
-- Factor bases
-------------------------------------------------------------------------------

rationalFactorBase :: Integer -> [Prime]
rationalFactorBase b1 = takeWhile (\p -> p <= b1) Prime.list

algebraicFactorBase :: Integer -> Zx -> [(Gfp,Prime)]
algebraicFactorBase b2 f =
    concatMap ideals $ takeWhile (\p -> p <= b2) Prime.list
  where
    ideals p = map (\r -> (r,p)) $ Gfpx.roots p (Gfpx.fromZx p f)

-------------------------------------------------------------------------------
-- Sieving
-------------------------------------------------------------------------------
