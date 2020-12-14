module Main
where

import qualified Factor.Zx as Zx
import Factor.Util

number :: Int
number = 7

main :: IO ()
main = do
    putStrLn $ underline ("First " ++ show number ++ " Swinnerton-Dyer Polynomials")
    mapM_ (putStrLn . ((:) '\n') . show) (take number Zx.swinnertonDyer)
