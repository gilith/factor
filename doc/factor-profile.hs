module Main
where

import Data.Time (UTCTime,defaultTimeLocale,diffUTCTime,parseTimeM)
import System.Environment (getArgs)
import System.IO (hGetContents)
import qualified System.Process as Process
import qualified Text.Regex as Regex
import Text.Printf (printf)

import Factor.Util

-------------------------------------------------------------------------------
-- Constants
-------------------------------------------------------------------------------

--
-- These ECM parameters require an overnight run
--

ecmWidth :: [Width]
ecmWidth = [20,25..75]

ecmBatch :: Int
ecmBatch = 10

--
-- These NFS parameters require an overnight run
--

nfsWidth :: [Width]
nfsWidth = [20,25..75]

nfsBatch :: Int
nfsBatch = 10

-------------------------------------------------------------------------------
-- Launching the factor executable
-------------------------------------------------------------------------------

factorSize :: Int -> String
factorSize w = "P[" ++ s ++ "] * P[" ++ s ++ "]" where s = show w

factorOutput :: String -> IO [String]
factorOutput exe = do
    (Nothing, Nothing, Just fperr, _) <- Process.createProcess fp
    lines <$> hGetContents fperr
  where
    fp = (Process.shell $ "/usr/bin/time -f '%U %S %M' " ++ exe)
           {Process.std_in = Process.NoStream,
            Process.std_out = Process.NoStream,
            Process.std_err = Process.CreatePipe}

-------------------------------------------------------------------------------
-- Extracting information from a log
-------------------------------------------------------------------------------

type Match a = String -> Maybe a
type Parse a = [String] -> Maybe (a,[String])

parseMatch :: Match a -> Parse a
parseMatch f = go
  where
    go [] = Nothing
    go (s : l) = case f s of { Just x -> Just (x,l) ; Nothing -> go l }

parseAll :: Parse a -> Parse [a]
parseAll p = Just . go
  where go l = case p l of
                 Just (a,l') -> (a : al, l'') where (al,l'') = go l'
                 Nothing -> ([],l)

matchMap :: (a -> Maybe b) -> Match a -> Match b
matchMap f m s = case m s of
                   Nothing -> Nothing
                   Just a -> f a

matchRead :: Read a => Match a
matchRead s = case reads s of { [(a,"")] -> Just a ; _ -> Nothing }

matchRegex :: String -> Match String
matchRegex = match . Regex.mkRegex
  where
    match r s = case Regex.matchRegex r s of
                  Nothing -> Nothing
                  Just [x] -> Just x
                  Just l -> error $ "regex returned bad output" ++ show l

matchTimestamp :: Match UTCTime
matchTimestamp = parseTimeM True defaultTimeLocale timestampFormat

matchTimestampRegex :: String -> Match UTCTime
matchTimestampRegex r = matchMap matchTimestamp $ matchRegex $ "^([[][[:digit:]]{4}-[[:digit:]]{2}-[[:digit:]]{2} [[:digit:]]{2}:[[:digit:]]{2}:[[:digit:]]{2}[]]) " ++ r

matchRegexPrefix :: String -> Match String
matchRegexPrefix s = matchRegex $ "^" ++ s ++ "(.*)$"

matchExact :: String -> Match ()
matchExact t m = if m == t then Just () else Nothing

-------------------------------------------------------------------------------
-- Time and memory profiling
-------------------------------------------------------------------------------

type Seconds = Double
type Bytes = Double
type Profile = (Seconds,Bytes)

diffUtc :: UTCTime -> UTCTime -> Seconds
diffUtc t u = realToFrac $ diffUTCTime t u

parseProfile :: [String] -> Maybe Profile
parseProfile [] = Nothing
parseProfile l = matchProfile (last l)

matchProfile :: Match Profile
matchProfile s =
    case words s of
      [uw,sw,mw] ->
        case (matchRead uw, matchRead sw, matchRead mw) of
          (Just u, Just s, Just m) -> Just (u + s, 1024.0 * fromIntegral m)
          _ -> Nothing
      _ -> Nothing

reportProfile :: Profile -> String
reportProfile (t,m) = timeReport t ++ " " ++ memoryReport m

timeReport :: Seconds -> String
timeReport s =
    if s < 1.0 then "Instant"
    else if s < 120.0 then show (floor s) ++ "s"
    else if m < 120.0 then show (floor m) ++ "m"
    else show (floor h) ++ "h"
  where
    m = s / 60.0
    h = m / 60.0

memoryReport :: Bytes -> String
memoryReport b =
    if b < 1.0 then "0"
    else if b < 256.0 then show (floor b) ++ "B"
    else if k < 256.0 then mem k ++ "K"
    else if m < 256.0 then mem m ++ "M"
    else mem g ++ "G"
  where
    k = b / 1024.0
    m = k / 1024.0
    g = m / 1024.0
    mem x | x < 10.0 = printf "%.1f" x
    mem x = show (floor x)

-------------------------------------------------------------------------------
-- Profiling ECM
-------------------------------------------------------------------------------

type Primes = Integer
type Curves = Integer

ecmArgs :: String
ecmArgs = " -v --ecm-primes -"

ecmParse :: [String] -> Maybe (Profile,Primes,Curves)
ecmParse out0 = do
    ((),out1) <- parseMatch (matchExact "Firing up the elliptic curve method (ECM)") out0
    -- Extract last reported number of primes
    (p0,out2) <- parseMatch (matchMap matchRead $ matchRegex "^Multiplying new curve points by first ([[:digit:]]+) primes$") out1
    (pl,out3) <- parseAll (parseMatch (matchMap matchRead $ matchRegex "^Multiplying by next [[:digit:]]+ primes to achieve target of ([[:digit:]]+)$")) out2
    p <- pure $ if null pl then p0 else last pl
    -- Extract last reported number of curve points
    (cl,_) <- parseAll (parseMatch (matchMap matchRead $ matchRegex "^Generating [[:digit:]]+ new curve points to achieve target of ([[:digit:]]+)$")) out1
    c <- if null cl then Nothing else Just $ last cl
    -- Factorization
    (_,out4) <- parseMatch (matchRegexPrefix "ECM factorization: ") out3
    prof <- parseProfile out4
    return (prof,p,c)

ecmInstance :: String -> IO (Maybe (Profile,Primes,Curves))
ecmInstance exe = do
    out <- factorOutput exe
    --putStr $ unlines out
    return $ ecmParse out

ecmReport :: Maybe (Profile,Primes,Curves) -> String
ecmReport Nothing = "Failed"
ecmReport (Just (prof,p,c)) =
    reportProfile prof ++ " " ++ show p ++ " " ++ show c

ecmSize :: String -> Width -> Int -> IO ()
ecmSize exe w n = do
    sz <- pure $ factorSize w
    putStrLn $ "\n" ++ sz
    fac <- pure $ exe ++ " '" ++ sz ++ "'"
    --putStrLn fac
    mapM_ (\_ -> (ecmReport <$> ecmInstance fac) >>= putStrLn) [1..n]

ecmProfile :: String -> IO ()
ecmProfile exe = do
    putStrLn $ underline "Factorization using the elliptic curve method (ECM)"
    putStrLn $ "Each section below named EXPR profiles " ++
               show ecmBatch ++ " invocations of"
    putStrLn $ "  factor" ++ ecmArgs ++ " 'EXPR'"
    putStrLn "Each invocation generates a line of results with the following fields:"
    putStrLn "- Total time spent"
    putStrLn "- Peak memory usage"
    putStrLn "- Number of primes used"
    putStrLn "- Number of curve points used"
    fac <- pure $ exe ++ ecmArgs
    mapM_ (\w -> ecmSize fac w ecmBatch) ecmWidth

-------------------------------------------------------------------------------
-- Profiling NFS
-------------------------------------------------------------------------------

nfsArgs :: String
nfsArgs = " -vt --ecm-primes 0"

nfsParse :: [String] -> Maybe (Profile,[Seconds])
nfsParse out0 = do
    (t0,out1) <- parseMatch (matchTimestampRegex "Cranking up the number field sieve [(]NFS[)]$") out0
    -- Select polynomial and factor bases
    (t1,out2) <- parseMatch (matchTimestampRegex "Searching for [[:digit:]+]+ = [[:digit:]]+ smooth elements of Z[[]w[]]:$") out1
    -- Sieve for smooth elements
    (t2,out3) <- parseMatch (matchTimestampRegex "Derivative of f is f'") out2
    -- Gaussian elimination
    (t3,out4) <- parseMatch (matchTimestampRegex "Considering square product ") out3
    -- Factorization
    (t4,out5) <- parseMatch (matchTimestampRegex "NFS factorization: ") out4
    prof <- parseProfile out5
    return (prof, [diffUtc t1 t0, diffUtc t2 t1, diffUtc t3 t2, diffUtc t4 t3])

nfsInstance :: String -> IO (Maybe (Profile,[Seconds]))
nfsInstance exe = do
    out <- factorOutput exe
    --putStr $ unlines out
    return $ nfsParse out

nfsReport :: Maybe (Profile,[Seconds]) -> String
nfsReport Nothing = "Failed"
nfsReport (Just (prof,ts)) =
    reportProfile prof ++ concatMap (\s -> " " ++ timeReport s) ts

nfsSize :: String -> Width -> Int -> IO ()
nfsSize exe w n = do
    sz <- pure $ factorSize w
    putStrLn $ "\n" ++ sz
    fac <- pure $ exe ++ " '" ++ sz ++ "'"
    --putStrLn fac
    mapM_ (\_ -> (nfsReport <$> nfsInstance fac) >>= putStrLn) [1..n]

nfsProfile :: String -> IO ()
nfsProfile exe = do
    putStrLn $ underline "Factorization using the number field sieve (NFS)"
    putStrLn $ "Each section below named EXPR profiles " ++
               show nfsBatch ++ " invocations of"
    putStrLn $ "  factor" ++ nfsArgs ++ " 'EXPR'"
    putStrLn "Each invocation generates a line of results with the following fields:"
    putStrLn "- Total time spent"
    putStrLn "- Peak memory usage"
    putStrLn "- Time spent selecting polynomial and factor bases"
    putStrLn "- Time spent sieving for smooth elements"
    putStrLn "- Time spent in Gaussian elimination"
    putStrLn "- Time spent computing rational and algebraic square roots"
    fac <- pure $ exe ++ nfsArgs
    mapM_ (\w -> nfsSize fac w nfsBatch) nfsWidth

-------------------------------------------------------------------------------
-- Top-level
-------------------------------------------------------------------------------

data Algorithm = ECM | NFS

readAlgorithm :: String -> Algorithm
readAlgorithm "ECM" = ECM
readAlgorithm "NFS" = NFS
readAlgorithm _ = usage

usage :: a
usage = error "usage: factor-profile {ECM|NFS} <factor-executable>"

main :: IO ()
main = do
    args <- getArgs
    (alg,exe) <- pure $ case args of
                          [a,e] -> (readAlgorithm a, e)
                          _ -> usage
    case alg of
      ECM -> ecmProfile exe
      NFS -> nfsProfile exe
