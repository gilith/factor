{- |
module: Factor.Util
description: Utility functions
license: MIT

maintainer: Joe Leslie-Hurd <joe@gilith.com>
stability: provisional
portability: portable
-}

module Factor.Util
where

import qualified Data.List as List

-------------------------------------------------------------------------------
-- Integer divides relation
-------------------------------------------------------------------------------

isUnit :: Integer -> Bool
isUnit 1 = True
isUnit (-1) = True
isUnit _ = False

divides :: Integer -> Integer -> Bool
divides _ 0 = True
divides 0 _ = False
divides m n = n `mod` m == 0

factor :: Integer -> Integer -> (Int,Integer)
factor m | m <= 1 = error "Integer factor: argument must be positive non-unit"
factor m | otherwise = \n -> if n == 0 then (0,0) else go 0 n
  where go k n = if divides m n then go (k+1) (n `div` m) else (k,n)

-------------------------------------------------------------------------------
-- Integer division
-------------------------------------------------------------------------------

division :: Integer -> Integer -> (Integer,Integer)
division _ 0 = error "Integer division by zero"
division m n = if r < 0 then (q + 1, r - n) else (q,r)
  where (q,r) = (m `div` n, m `mod` n)

divisionClosest :: Integer -> Integer -> (Integer,Integer)
divisionClosest m n =
    if abs_n < 2*r then (if n < 0 then q - 1 else q + 1, r - abs_n) else (q,r)
  where
    (q,r) = division m n
    abs_n = abs n

multiple :: Integer -> Integer -> Maybe Integer
multiple 0 = error "Integer multiple: division by 0"
multiple 1 = Just
multiple (-1) = Just . negate
multiple m = \n -> if divides m n then Just (n `div` m) else Nothing

-------------------------------------------------------------------------------
-- Integer greatest common divisor
-------------------------------------------------------------------------------

egcd :: Integer -> Integer -> (Integer,(Integer,Integer))
egcd m 0 = if m < 0 then (-m,(-1,0)) else (m,(1,0))
egcd m n =
    (g, (t, s - q*t))
  where
    (g,(s,t)) = egcd n r
    (q,r) = division m n

-------------------------------------------------------------------------------
-- Integer nth root function [1] satisfying
--
--  0 < n /\ 0 <= k /\ p = nthRoot n k
-- ------------------------------------
--        p^n <= k < (p+1)^n
--
-- 1. https://en.wikipedia.org/wiki/Nth_root_algorithm
-------------------------------------------------------------------------------

nthRoot :: Int -> Integer -> Integer
nthRoot 1 k = k
nthRoot _ 0 = 0
nthRoot n k = if k < n' then 1 else go (k `div` n')
  where
    n' = toInteger n
    go x = if x' >= x then x else go x'
      where
        x' = ((n' - 1) * x + k `div` (x ^ (n' - 1))) `div` n'

nthRootClosest :: Int -> Integer -> Integer
nthRootClosest n k =
    if (p+1)^n - k < k - p^n then p+1 else p
  where
    p = nthRoot n k

-------------------------------------------------------------------------------
-- Making lists
-------------------------------------------------------------------------------

singleton :: a -> [a]
singleton x = [x]

doubleton :: a -> a -> [a]
doubleton x y = [x,y]

tripleton :: a -> a -> a -> [a]
tripleton x y z = [x,y,z]

-------------------------------------------------------------------------------
-- Unfolding lists a fixed number of times
-------------------------------------------------------------------------------

unfoldrN :: (b -> (a,b)) -> Int -> b -> ([a],b)
unfoldrN f = go []
  where
    go xs 0 s = (reverse xs, s)
    go xs n s = go (x : xs) (n - 1) s' where (x,s') = f s

-------------------------------------------------------------------------------
-- Pretty-print a table
-------------------------------------------------------------------------------

data Table =
    Table
      {borderTable :: Bool,
       alignLeftTable :: Bool,
       paddingTable :: Int}
  deriving (Show)

fmtTable :: Table -> [[String]] -> String
fmtTable fmt table = concatMap ppRow rows
  where
    rows :: [(Int,[(Int,[String])])]
    rows = map mkRow table

    colWidths :: [Int]
    colWidths = foldr (maxWidths . map fst . snd) [] rows

    cols :: Int
    cols = length colWidths

    mkRow :: [String] -> (Int,[(Int,[String])])
    mkRow [] = (0,[])
    mkRow row = (maximum (map (length . snd) ents), ents)
      where ents = map mkEntry row

    mkEntry :: String -> (Int,[String])
    mkEntry ent = case lines ent of
                    [] -> (0,[])
                    l -> (maximum (map length l), l)

    ppRow :: (Int,[(Int,[String])]) -> String
    ppRow (_,[]) = (if border then hBorder else "") ++ "\n"
    ppRow (h,ents) = concat ls
      where
        row = ents ++ replicate (cols - length ents) (0,[])
        (ls,_) = unfoldrN peelRow h (zip colWidths row)

    peelRow :: [(Int,(Int,[String]))] -> (String, [(Int,(Int,[String]))])
    peelRow row = (l,row')
      where
        ((s,_),row') = List.mapAccumL (peelEntry . vBorder) ("",0) row
        l = (if border then tail s else s) ++ "\n"

    peelEntry :: (String,Int) -> (Int,(Int,[String])) ->
                 ((String,Int),(Int,(Int,[String])))
    peelEntry (s,k) (cw,(ew,[])) = ((s, k + cw + padding),(cw,(ew,[])))
    peelEntry (s,k) (cw, (ew, x : xs)) = (sk,(cw,(ew,xs)))
      where
        sk = if alignLeft then skl else skr
        skl = (s ++ replicate k ' ' ++ x, (cw + padding) - xw)
        skr = (s ++ replicate ((k + cw) - ew) ' ' ++ x, (ew + padding) - xw)
        xw = length x

    vBorder :: (String,Int) -> (String,Int)
    vBorder (s,k) | border = (s ++ replicate k ' ' ++ "|", padding)
    vBorder (s,k) | otherwise = (s,k)

    hBorder :: String
    hBorder = tail $ concatMap sep colWidths
      where sep w = "+" ++ replicate (w + 2 * padding) '-'

    border :: Bool
    border = borderTable fmt

    alignLeft :: Bool
    alignLeft = alignLeftTable fmt

    padding :: Int
    padding = paddingTable fmt

    maxWidths :: [Int] -> [Int] -> [Int]
    maxWidths r1 r2 =
      zipWith max r1 r2 ++
      (case compare (length r1) (length r2) of
         LT -> drop (length r1) r2
         EQ -> []
         GT -> drop (length r2) r1)

ppTable :: [[String]] -> String
ppTable = fmtTable (Table True False 2)
