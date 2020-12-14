module Main
where

import qualified Factor.Prime as Prime
import Factor.Util

fac :: Int -> Int -> Int
fac n c =
    last (takeWhile (\t -> Prime.smoothProbTrials b t (2^c) > -1.0) [1..])
  where
    b = exp2Integer (Prime.nthPrimeEstimate (fromIntegral n))

tab :: [Int] -> [Int] -> [[String]]
tab ns cs =
    ("" : "|" : map show ns) :
    (map (\c -> show c : "|" : map (\n -> show (fac n c)) ns) cs)

main :: IO ()
main = do
    putStrLn $ underline "Table Legend"
    putStrLn "x-axis:  number of primes (base 2 log)"
    putStrLn "y-axis:  number of curve points (base 2 log)"
    putStrLn "entries: largest factor bitwidth that ECM can find with probability at least 50%"
    putStrLn ""
    putStr $ fmtTable (Table False False 1) (tab [1..40] [1..45])
