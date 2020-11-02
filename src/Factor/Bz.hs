{- |
module: Factor.Bz
description: The Berlekamp-Zassenhaus algorithm for factoring in Z[x]
license: MIT

maintainer: Joe Leslie-Hurd <joe@gilith.com>
stability: provisional
portability: portable
-}
module Factor.Bz
where

import qualified Data.List as List

import Factor.Gfpx (Gfpx)
import qualified Factor.Gfpx as Gfpx
import Factor.Prime (Prime)
import qualified Factor.Prime as Prime
import Factor.Util
import Factor.Zx (Zx)
import qualified Factor.Zx as Zx

-------------------------------------------------------------------------------
-- The Landau-Mignotte bound on the absolute value of factor coefficients
--
-- https://www.math.fsu.edu/~hoeij/papers/issac11/A.pdf
-------------------------------------------------------------------------------

factorCoeffBound :: Zx -> Integer
factorCoeffBound f | Zx.isZero f =
    error "Z[x] factor coefficient bound is undefined for zero"
factorCoeffBound f =
    nthRoot 2 (d + 1) * (2 ^ d) * m
  where
    d = toInteger (Zx.degree f)
    m = maximum (map (abs . snd) (Zx.monomials f))

-------------------------------------------------------------------------------
-- Finding factors modulo a suitable prime p
-------------------------------------------------------------------------------

monicGfpx :: Prime -> Zx -> Gfpx
monicGfpx p = snd . Gfpx.constMonic p . Gfpx.fromZx p

suitablePrime :: Zx -> Prime
suitablePrime f = head $ filter suitable Prime.primes
  where
    suitable p = not (divides p c) && Gfpx.squareFree p (monicGfpx p f)
    c = Zx.leadingCoeff f

-------------------------------------------------------------------------------
-- Hensel lifting factors modulo p^k
--
-- https://www.csd.uwo.ca/~mmorenom/CS874/Lectures/Newton2Hensel.html/node17.html
-------------------------------------------------------------------------------

henselLiftQuadratic :: Zx -> (Integer,(Gfpx,Gfpx,Gfpx,Gfpx)) ->
                       (Integer,(Gfpx,Gfpx,Gfpx,Gfpx))
henselLiftQuadratic f (m,(g,h,s,t)) = (m',(g',h',s',t'))
  where
    m' = m * m
    e = Gfpx.subtract m' (Gfpx.fromZx m' f) (Gfpx.multiply m' g h)
    (q,r) = Gfpx.division m' (Gfpx.multiply m' s e) h
    g' = Gfpx.sum m' [g, Gfpx.multiply m' t e, Gfpx.multiply m' q g]
    h' = Gfpx.add m' h r
    b = Gfpx.subtract m'
          (Gfpx.add m' (Gfpx.multiply m' s g') (Gfpx.multiply m' t h'))
          Gfpx.one
    (c,d) = Gfpx.division m' (Gfpx.multiply m' s b) h'
    s' = Gfpx.subtract m' s d
    t' = Gfpx.subtract m'
           (Gfpx.multiply m' t (Gfpx.subtract m' Gfpx.one b))
           (Gfpx.multiply m' c g')

henselLiftModulus :: Zx -> Prime -> (Int,Integer)
henselLiftModulus f p =
    head $ List.dropWhile (\(_,pk) -> pk < b) $
    iterate (\(k,pk) -> (k + 1, pk * pk)) (0,p)
  where
    b = 2 * factorCoeffBound f + 1

henselLiftFactors :: Zx -> Prime -> Int -> [Gfpx] -> [Gfpx]
henselLiftFactors f0 p k = go [] f0
  where
    go _ _ [] = error "no factors to Hensel lift"
    go _ _ [_] = error "single factor to Hensel lift"
    go acc f (g : gs) =
        if length gs <= 1 then reverse acc ++ [gk,hk]
        else go (gk : acc) (Gfpx.toZx hk) gs
      where
        h = Gfpx.product p gs
        (_,(s,t)) = Gfpx.egcd p g h
        (_,(gk,hk,_,_)) = iterate (henselLiftQuadratic f) (p,(g,h,s,t)) !! k

-------------------------------------------------------------------------------
-- Recombining factors mod p^k to find true factors in Z[x]
--
-- https://en.wikipedia.org/wiki/Factorization_of_polynomials
-- https://www.math.fsu.edu/~hoeij/papers/issac11/A.pdf
-------------------------------------------------------------------------------

recombineFactors :: Zx -> Integer -> [Gfpx] -> [Zx]
recombineFactors f pk =
    \hs -> case length hs of
             0 -> []
             1 -> [f]
             _ -> go [(Gfpx.fromZx pk (Zx.constant c), [], hs)]
  where
    c = Zx.leadingCoeff f
    d = Zx.degree f
    db = d `div` 2

    -- Check every subset of hs with degree sum at most db
    -- If s is a subset of t, then check s before t
    go [] = [f]
    go ((_,_,[]) : wl) = go wl
    go ((g, gs, h : hs) : wl) = check g h gs hs (g, h : gs, hs) wl

    check g h gs hs w wl =
        if Gfpx.degree g + Gfpx.degree h > db then go (w : wl)
        else if Zx.divides gz f then gz : recombineFactors f' pk (gs ++ hs)
        else go (w : (g',gs,hs) : wl)
      where
        g' = Gfpx.multiply pk g h
        gz = Zx.primitive $ Gfpx.toSmallestZx pk g'
        f' = Zx.quotient f gz

-------------------------------------------------------------------------------
-- Factorization using the Berlekamp-Zassenhaus algorithm
--
-- https://en.wikipedia.org/wiki/Factorization_of_polynomials
-- https://www.math.fsu.edu/~hoeij/papers/issac11/A.pdf
-------------------------------------------------------------------------------

factorSquareFree :: Zx -> [Zx]
factorSquareFree f | Zx.isOne f = []
factorSquareFree f | Zx.isLinear f = [f]
factorSquareFree f =
    if length gs <= 1 then [f] else recombineFactors f pk hs
  where
    p = suitablePrime f
    g = monicGfpx p f
    gs = Gfpx.factorSquareFreeBerlekamp p g
    (k,pk) = henselLiftModulus f p
    hs = henselLiftFactors (Gfpx.toZx (monicGfpx pk f)) p k gs

factorPrimitive :: Zx -> [(Zx,Integer)]
factorPrimitive = concat . zipWith fsf [1..] . Zx.squareFreeDecomposition
  where fsf k = map (\g -> (g,k)) . factorSquareFree

factor :: Zx -> (Integer,[(Zx,Integer)])
factor f = (c, factorPrimitive g)
  where (c,g) = Zx.contentPrimitive f

-------------------------------------------------------------------------------
-- Irreducibility test
-------------------------------------------------------------------------------

irreducible :: Zx -> Bool
irreducible f =
    Zx.isPrimitive f &&
    Zx.squareFree f &&
    length (factorSquareFree f) == 1

{-
ghci Factor/Bz.hs
:break factorSquareFree
factor $ Zx.fromCoeff [4,47,-2,-23,18,10]
factor $ Zx.swinnertonDyer !! 4
factor $ Zx.multiply (Zx.swinnertonDyer !! 3) (Zx.swinnertonDyer !! 4)
factor $ Zx.multiply (Zx.fromCoeff [2,-2]) (Zx.fromCoeff [-3,3])
:show bindings
-}
