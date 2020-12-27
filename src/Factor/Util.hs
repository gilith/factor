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

import Control.Monad (ap,liftM)
import qualified Data.Bits as Bits
import qualified Data.List as List
import Data.Maybe (isJust)
import qualified Data.Time as Time
import System.IO (hPutStrLn,stderr)
import System.Random (RandomGen)
import qualified System.Random as Random

-------------------------------------------------------------------------------
-- Factoring monad
-------------------------------------------------------------------------------

type Factor f a = Either f a

runFactor :: Show f => Factor f a -> a
runFactor (Left f) = error $ "found a factor " ++ show f
runFactor (Right a) = a

-------------------------------------------------------------------------------
-- Verbose monad
-------------------------------------------------------------------------------

data Verbose a =
    ResultVerbose a
  | CommentVerbose String (Verbose a)

instance Functor Verbose where
  fmap = liftM

instance Applicative Verbose where
  pure = ResultVerbose
  (<*>) = ap

instance Monad Verbose where
  ResultVerbose a >>= f = f a
  CommentVerbose s v >>= f = CommentVerbose s (v >>= f)

timestampFormat :: String
timestampFormat = "[%Y-%m-%d %H:%M:%S]"

comment :: String -> Verbose ()
comment s = CommentVerbose s (ResultVerbose ())

runQuiet :: Verbose a -> a
runQuiet (ResultVerbose a) = a
runQuiet (CommentVerbose _ v) = runQuiet v

runVerbose :: Verbose a -> IO a
runVerbose (ResultVerbose a) = return a
runVerbose (CommentVerbose s v) = do { hPutStrLn stderr s ; runVerbose v }

runTimestampVerbose :: Verbose a -> IO a
runTimestampVerbose (ResultVerbose a) = return a
runTimestampVerbose (CommentVerbose s v) = do
    mapM_ stamp $ lines s
    runTimestampVerbose v
  where
    stamp l = do
        t <- fmt <$> Time.getZonedTime
        hPutStrLn stderr $ t ++ " " ++ l

    fmt = Time.formatTime Time.defaultTimeLocale timestampFormat

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

properDivisor :: Integer -> Integer -> Bool
properDivisor m n = divides m n && not (isUnit m) && abs m /= abs n

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

exactQuotient :: Integer -> Integer -> Maybe Integer
exactQuotient 0 = error "Integer exact quotient: division by 0"
exactQuotient 1 = Just
exactQuotient (-1) = Just . negate
exactQuotient m = \n -> if divides m n then Just (n `div` m) else Nothing

divPower :: Integer -> Integer -> (Integer,Integer)
divPower m | m <= 1 = error "divPower argument must be positive non-unit"
divPower m | otherwise = \n -> if n == 0 then (0,0) else go 0 n
  where go k n = if divides m n then go (k+1) (n `div` m) else (k,n)

-------------------------------------------------------------------------------
-- Integer factorial
-------------------------------------------------------------------------------

factorial :: Integer -> Integer
factorial n | n <= 1 = 1
factorial n = n * factorial (n - 1)

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

coprime :: Integer -> Integer -> Bool
coprime m n = gcd m n == 1

chineseRemainder :: Integer -> Integer -> Integer -> Integer -> Integer
chineseRemainder m n =
    \i j -> (i*tn + j*sm) `mod` mn
  where
    (_,(s,t)) = egcd m n
    mn = m * n
    sm = s * m
    tn = t * n

-------------------------------------------------------------------------------
-- Integer nth root function [1] satisfying
--
--  0 < n /\ 0 <= k /\ p = nthRoot n k
-- ------------------------------------
--        p^n <= k < (p+1)^n
--
-- 1. https://en.wikipedia.org/wiki/Nth_root_algorithm
-------------------------------------------------------------------------------

nthRoot :: Integer -> Integer -> Integer
nthRoot 1 k = k
nthRoot _ 0 = 0
nthRoot n k = if k < n' then 1 else go (k `div` n')
  where
    n' = toInteger n
    go x = if x' >= x then x else go x'
      where
        x' = ((n' - 1) * x + k `div` (x ^ (n' - 1))) `div` n'

nthRootClosest :: Integer -> Integer -> Integer
nthRootClosest n k =
    if (p+1)^n - k < k - p^n then p+1 else p
  where
    p = nthRoot n k

-------------------------------------------------------------------------------
-- Integer powers
-------------------------------------------------------------------------------

destNthPower :: Integer -> Integer -> Maybe Integer
destNthPower n k = if r ^ n == k then Just r else Nothing
  where r = nthRoot n k

isNthPower :: Integer -> Integer -> Bool
isNthPower n = isJust . destNthPower n

destSquare :: Integer -> Maybe Integer
destSquare = destNthPower 2

isSquare :: Integer -> Bool
isSquare = isNthPower 2

-------------------------------------------------------------------------------
-- Integer bits
-------------------------------------------------------------------------------

type Width = Int

-- Caution: returns an infinite list for negative arguments
bitsInteger :: Integer -> [Bool]
bitsInteger = map odd . takeWhile ((/=) 0) . iterate (flip Bits.shiftR 1)

widthInteger :: Integer -> Width
widthInteger n | n < 0 = error "width only defined for nonnegative integers"
widthInteger n | otherwise = length $ bitsInteger n

widthIntegerToString :: Integer -> String
widthIntegerToString n = show (widthInteger n) ++ "-bit integer " ++ show n

uniformInteger :: RandomGen r => Width -> r -> (Integer,r)
uniformInteger w | w < 0 = error $ "no integers with width " ++ show w
uniformInteger 0 = (,) 0
uniformInteger w = gen (w - 1) 1
  where
    gen 0 n r = (n,r)
    gen i n r = gen (i - 1) (2 * n + (if b then 1 else 0)) r'
      where (b,r') = Random.random r

uniformOddInteger :: RandomGen r => Width -> r -> (Integer,r)
uniformOddInteger w _ | w < 1 = error $ "no odd integers with width " ++ show w
uniformOddInteger w r = (2*n + 1, r')
  where (n,r') = uniformInteger (w - 1) r

-------------------------------------------------------------------------------
-- Base 2 log
-------------------------------------------------------------------------------

type Log2Integer = Double
type Log2Probability = Double

log2 :: Double -> Double
log2 = logBase 2.0

log2e :: Double
log2e = log2 (exp 1.0)

log2Integer :: Integer -> Log2Integer
log2Integer n | n <= 0 = error "log only defined for positive integers"
log2Integer n =
    fromInteger (toInteger k) + log2 (fromInteger (Bits.shiftR n k))
  where
    k = if w <= p then 0 else w - p
    w = widthInteger n
    p = 53

logInteger :: Integer -> Double
logInteger n = log2Integer n / log2e

exp2Integer :: Log2Integer -> Integer
exp2Integer x = floor (2.0 ** x)

-------------------------------------------------------------------------------
-- The Jacobi symbol (m/n)
--
-- The n argument must be a positive odd integer
-------------------------------------------------------------------------------

data Residue = Residue | NonResidue | ZeroResidue
  deriving (Eq,Ord,Show)

multiplyResidue :: Residue -> Residue -> Residue
multiplyResidue ZeroResidue _ = ZeroResidue
multiplyResidue _ ZeroResidue = ZeroResidue
multiplyResidue r1 r2 = if r1 == r2 then Residue else NonResidue

jacobiSymbol :: Integer -> Integer -> Residue
jacobiSymbol =
    \m n -> if n == 1 then Residue else go False m n
  where
    go f m n =  -- Invariant: n is a positive odd integer greater than 1
        if p == 0 then ZeroResidue
        else if s == 1 then if g then NonResidue else Residue
        else go h n s
      where
        p = m `mod` n
        (r,s) = divPower 2 p
        n8 = n `mod` 8
        n8_17 = n8 == 1 || n8 == 7
        n4_1 = n8 == 1 || n8 == 5
        s4_1 = s `mod` 4 == 1
        g = if even r || n8_17 then f else not f
        h = if n4_1 || s4_1 then g else not g

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

unfoldlN :: (b -> (a,b)) -> Int -> b -> ([a],b)
unfoldlN f = go
  where
    go 0 s = ([],s)
    go n s = (x : xs, u)
      where
        (x,t) = f s
        (xs,u) = go (n - 1) t

unfoldrN :: (b -> (a,b)) -> Int -> b -> ([a],b)
unfoldrN f = go []
  where
    go xs 0 s = (xs,s)
    go xs n s = go (x : xs) (n - 1) s' where (x,s') = f s

-------------------------------------------------------------------------------
-- Abbreviated lists
-------------------------------------------------------------------------------

unabbrevList :: [String] -> String
unabbrevList = concatMap (\x -> "\n  " ++ x)

abbrevList :: String -> [String] -> String
abbrevList s l = unabbrevList m
  where
    i = 3
    m = take i l ++ (if n <= 2*i + 1 then drop i l else o ++  drop (n - i) l)
    o = ["[... " ++ show (n - 2*i) ++ " omitted " ++ s ++ " ...]"]
    n = length l

-------------------------------------------------------------------------------
-- Underlining
-------------------------------------------------------------------------------

underline :: String -> String
underline s = s ++ "\n" ++ replicate (length s) '-'

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
    ppRow (h,ents) = concat (reverse ls)
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
