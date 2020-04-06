{- |
module: Factor.Nfzw
description: The subring Z[w] of the number field Q(w)
license: MIT

maintainer: Joe Leslie-Hurd <joe@gilith.com>
stability: provisional
portability: portable
-}
module Factor.Nfzw
where

import qualified Factor.Gfpx as Gfpx
import Factor.Prime (Gfp,Prime)
import qualified Factor.Prime as Prime
import Factor.Util
import Factor.Zx (Zx)
import qualified Factor.Zx as Zx

-------------------------------------------------------------------------------
-- Elements of Z[w] having the form a + b*w with a and b coprime integers
-------------------------------------------------------------------------------

data Nfzw = Nfzw Integer Integer
  deriving (Eq,Ord)

instance Show Nfzw where
  show x = case x of
             Nfzw a 0 -> show a
             Nfzw 0 b -> showW b
             Nfzw a b | b < 0 -> show a ++ " - " ++ showW (-b)
             Nfzw a b | otherwise -> show a ++ " + " ++ showW b
    where
      showW 1 = "w"
      showW (-1) = "-w"
      showW i = show i ++ "w"

valid :: Nfzw -> Bool
valid (Nfzw 0 0) = True
valid (Nfzw a b) = coprime a b

-------------------------------------------------------------------------------
-- All valid elements a + bw where b > 0
-------------------------------------------------------------------------------

list :: [Nfzw]
list = filter valid $ concatMap line [0..]
  where line k = map (\a -> Nfzw a (k + 1 - abs a)) [(-k)..k]

-------------------------------------------------------------------------------
-- Ring operations
-------------------------------------------------------------------------------

zero :: Nfzw
zero = Nfzw 0 0

isZero :: Nfzw -> Bool
isZero x = x == zero

negate :: Nfzw -> Nfzw
negate (Nfzw a b) = Nfzw (Prelude.negate a) (Prelude.negate b)

-------------------------------------------------------------------------------
-- Ring homomorphisms from a + bw to Z
-------------------------------------------------------------------------------

toInteger :: Integer -> Nfzw -> Integer
toInteger m (Nfzw a b) = a + b*m

-------------------------------------------------------------------------------
-- The norm of an element a - bw is b^degree(f) * f(a/b)
-------------------------------------------------------------------------------

norm :: Zx -> Nfzw -> Integer
norm f (Nfzw a b) =
    fst $ align 0 $ foldr fma (0,0,1) $ Zx.monomials f
  where
    fma (i,c) z = (i, ni + c*bi, bi) where (ni,bi) = align i z

    align i (d,nd,bd) = if k <= 0 then (nd,bd) else (ni,bi)
      where
        k = d - i
        ni = nd * a^k
        bi = bd * b'^k

    b' = Prelude.negate b

-------------------------------------------------------------------------------
-- First degree prime ideals of Z[w]
--
-- These have norm p for some prime integer p, and are in bijective
-- correspondence with pairs (r,p) where f(r) == 0 (mod p)
--
-- Elements of the form a + b*w have the property that their principal
-- ideal uniquely factors into first degree prime ideals
--
--   <a + b*w> == (r1,p1)^e1 * ... * (rn,pn)^en
--
-- where
--
--   |norm (a + b*w)| == p1^e1 * ... * pn^en
--
-- and
--
--   a + b*ri == 0 (mod pi) for every 1 <= i <= n
--
-- Note that this last property implies that the pi are all distinct
-- prime integers, since at most one value of r can satisfy the
-- equation.
-------------------------------------------------------------------------------

type Ideal = (Gfp,Prime)

ideals :: Zx -> [Ideal]
ideals f =
    concatMap roots Prime.list
  where
    roots p = map (\r -> (r,p)) $ Gfpx.roots p (Gfpx.fromZx p f)

inIdeal :: Nfzw -> Ideal -> Bool
inIdeal (Nfzw a b) (r,p) =
    Prime.add p a' (Prime.multiply p r b') == 0
  where
    a' = Prime.fromInteger p a
    b' = Prime.fromInteger p b

factor :: Zx -> [Ideal] -> Nfzw -> ([(Ideal,Int)],Integer)
factor f rps0 x = go rps0 (norm f x)
  where
    go _ n | abs n <= 1 = ([],n)
    go [] n = ([],n)
    go (rp : rps) n = (if k == 0 then rpks else rpk : rpks, s)
      where
        p = snd rp
        (k,m) = divPower p n
        (rpks,s) = go rps2 m
        (rps1,rps2) = span ((==) p . snd) rps
        rpk = case filter (inIdeal x) (rp : rps1) of
                [] -> error "no ideal divides x"
                [i] -> (i,k)
                _ : _ : _ -> error "multiple ideals divide x"
