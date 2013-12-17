-- Lucas Pena
-- Tayler Mandel
-- 2-3 Trees

{-# LANGUAGE InstanceSigs, GADTs, DataKinds, KindSignatures #-}

module TwoThree where

--import Persistent

import Control.Monad
import Test.QuickCheck hiding (elements)
import Data.Maybe as Maybe
import Data.List (sort, nub)

data Nat = Z | S Nat

data Tree (h :: Nat) (a :: *) where           
  E  :: Tree Z a
  N2 :: a -> Tree h a -> Tree h a -> Tree (S h) a
  N3 :: a -> a -> Tree h a -> Tree h a -> Tree h a -> Tree (S h) a
  
instance Show a => Show (Tree h a) where
  show E = "E"
  show (N2 x t1 t2) = 
    "(N2 " ++ show x ++ " " ++ show t1 ++ " " ++ show t2 ++ ")"
  show (N3 x y t1 t2 t3) =
    "(N3 " ++ show x ++ " " ++ show y ++ " " ++ 
    show t1 ++ " " ++ show t2 ++ " " ++ show t3 ++ ")"
  
data TTT a where
  Root :: Tree h a -> TTT a
    
instance Show a => Show (TTT a) where
  show (Root t) = show t
           
{- 
Invariants:
  1. Every non-leaf node is a 2-node (N2) or a 3-node (N3).
  2. A 2-node contains 1 data item and has 2 children.
  3. A 3-node contains 2 data items and has 3 children.
  4. All leaf nodes are at the same level.
  5. All data are kept in sorted order (BST invariant).
  6. Every leaf node will contain 1 or 2 fields.
-}

-- Fourth invariant
prop_tree :: TTT Int -> Bool
prop_tree (Root t) = aux t where
  aux :: Tree h a -> Bool
  aux E                 = True
  aux (N2 _ E E)        = True
  aux (N2 _ E _)        = False
  aux (N2 _ _ E)        = False
  aux (N2 _ t1 t2)      = aux t1 && aux t2
  aux (N3 _ _ E E E)    = True
  aux (N3 _ _ E _ _)    = False
  aux (N3 _ _ _ E _)    = False
  aux (N3 _ _ _ _ E)    = False
  aux (N3 _ _ t1 t2 t3) = aux t1 && aux t2 && aux t3
          
prop_balanced :: TTT Int -> Bool         
prop_balanced (Root t) = fst $ aux t where
  aux :: Tree h a -> (Bool, Int)
  aux E                 = (True, 0)
  aux (N2 _ t1 t2)      = (b1 && b2 && h1 == h2, h1 + 1) where 
    (b1, h1) = aux t1
    (b2, h2) = aux t2
  aux (N3 _ _ t1 t2 t3) = (b1 && b2 && b3 && h1 == h2 && h2 == h3, h1 + 1) where
    (b1, h1) = aux t1
    (b2, h2) = aux t2
    (b3, h3) = aux t3

-- Fifth invariant
prop_BST :: TTT Int -> Bool
prop_BST t = nub (sort x) == x where x = elements t

-- QuickCheck
instance (Ord a, Arbitrary a) => Arbitrary (TTT a) where
  arbitrary = liftM (foldr insert empty) arbitrary

-- TODO(lpena): add more tests to main
main :: IO ()
main = do quickCheck $ prop_tree
          quickCheck $ prop_BST
          
-- Implementation
empty :: TTT a
empty = Root E

member :: Ord a => a -> TTT a -> Bool
member x (Root t) = aux x t where
  aux :: Ord a => a -> Tree h a -> Bool
  aux _ E = False
  aux x (N2 y t1 t2) | x == y    = True
                     | x < y     = aux x t1
                     | otherwise = aux x t2
  aux x (N3 y z t1 t2 t3) | x == y || x == z = True
                          | x < y            = aux x t1
                          | x > z            = aux x t3
                          | otherwise        = aux x t2

elements :: Ord a => TTT a -> [a]
elements (Root t) = aux t [] where
  aux :: Ord a => Tree h a -> [a] -> [a]
  aux E acc                 = acc
  aux (N2 x t1 t2) acc      = aux t1 (x : aux t2 acc)
  aux (N3 x y t1 t2 t3) acc = aux t1 (x : aux t2 (y : aux t3 acc))

data IR h a = Same (Tree h a) | Diff a (Tree h a) (Tree h a) | Less (Small h a)

data Small (h :: Nat) a where
  DT :: Tree h a -> Small (S h) a

insert :: Ord a => a -> TTT a -> TTT a
insert x (Root t) = fix (ins x t) where 
  fix (Same t)       = Root t
  fix (Diff a t1 t2) = Root (N2 a t1 t2) 

ins :: Ord a => a -> Tree h a -> IR h a
ins x E = Diff x E E
ins x (N2 y E E) 
  | x == y    = Same $ N2 y E E
  | x < y     = Same $ N3 x y E E E
  | otherwise = Same $ N3 y x E E E
ins x (N3 y z E E E) 
  | x == y || x == z = Same $ N3 y z E E E
  | x < y            = Diff y (N2 x E E) (N2 z E E)
  | x > z            = Diff z (N2 y E E) (N2 x E E)
  | otherwise        = Diff x (N2 y E E) (N2 z E E)
ins x (N2 y t1 t2) 
  | x == y = Same $ N2 y t1 t2
  | x < y = case ins x t1 of
     Same t'       -> Same $ N2 y t' t2
     Diff v t' t'' -> Same $ N3 v y t' t'' t2
  | otherwise = case ins x t2 of
     Same t'       -> Same $ N2 y t1 t'
     Diff v t' t'' -> Same $ N3 y v t1 t' t''
ins x (N3 y z t1 t2 t3) 
  | x == y || x == z = Same $ N3 y z t1 t2 t3
  | x < y = case ins x t1 of
     Same t'       -> Same $ N3 y z t' t2 t3
     Diff v t' t'' -> Diff y (N2 v t' t'') (N2 z t2 t3)
  | x > z = case ins x t3 of
     Same t'       -> Same $ N3 y z t1 t2 t'
     Diff v t' t'' -> Diff z (N2 y t1 t2) (N2 v t' t'')
  | otherwise = case ins x t2 of
     Same t'       -> Same $ N3 y z t1 t' t3
     Diff v t' t'' -> Diff v (N2 y t1 t') (N2 z t'' t3)
