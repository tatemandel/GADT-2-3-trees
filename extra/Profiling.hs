-- Lucas Pena
-- Tayler Mandel
-- Profiling

module Main where

import RedBlack as RBT
import TwoThree as TTT

list1 :: [Int]
list1 = [1 .. 10000]

list2 :: [Int]
list2 = [5000 .. 10000] ++ [1 .. 4999]

profileTTT :: TTT Int
profileTTT = foldr TTT.delete bigTTT list2 where
  bigTTT = foldr TTT.insert TTT.empty list1

profileRBT :: RBT Int
profileRBT = foldr RBT.delete bigRBT list2 where
  bigRBT = foldr RBT.ins RBT.E list1

main :: IO ()
main = do print profileTTT
          print profileRBT