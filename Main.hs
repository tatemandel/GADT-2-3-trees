-- Lucas Pena
-- Tayler Mandel
-- 2-3 Trees

{-# OPTIONS -Wall -fwarn-tabs -fno-warn-type-defaults #-}
{-# LANGUAGE InstanceSigs, GADTs, DataKinds, KindSignatures #-}

module Main where

import Control.Monad
import Test.QuickCheck hiding (elements)
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
          
-- Implementation
empty :: TTT a
empty = Root E

member :: Ord a => a -> TTT a -> Bool
member x (Root t) = aux x t where
  aux :: Ord a => a -> Tree h a -> Bool
  aux _ E = False
  aux v (N2 y t1 t2) | v == y    = True
                     | v < y     = aux v t1
                     | otherwise = aux v t2
  aux v (N3 y z t1 t2 t3) | v == y || v == z = True
                          | v < y            = aux v t1
                          | v > z            = aux v t3
                          | otherwise        = aux v t2

-- Elements of the 2-3 tree in a list
elements :: Ord a => TTT a -> [a]
elements (Root t) = aux t [] where
  aux :: Ord a => Tree h a -> [a] -> [a]
  aux E acc                 = acc
  aux (N2 x t1 t2) acc      = aux t1 (x : aux t2 acc)
  aux (N3 x y t1 t2 t3) acc = aux t1 (x : aux t2 (y : aux t3 acc))
  
data IR h a = Same (Tree h a) | Diff a (Tree h a) (Tree h a)

-- Inserting an element in a 2-3 tree
insert :: Ord a => a -> TTT a -> TTT a
insert x (Root t) = fix (ins x t) where 
  fix (Same k)       = Root k
  fix (Diff a t1 t2) = Root (N2 a t1 t2) 

-- Helper function for insert
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

data IRD h a where
  SameD :: Tree h a -> IRD h a
  DiffD :: Tree h a -> IRD (S h) a

-- Delete element from 2-3 tree
delete :: Ord a => a -> TTT a -> TTT a
delete x (Root t) = fix (del x t) where
  fix (SameD k) = Root k
  fix (DiffD k) = Root k

-- Helper function for delete
del :: Ord a => a -> Tree h a -> IRD h a
del _ E = SameD E
del x (N2 y E E)
  | x == y = DiffD E
  | otherwise = SameD $ N2 y E E
del x (N3 y z E E E)
  | x == y = SameD $ N2 z E E
  | x == z = SameD $ N2 y E E
  | otherwise = SameD $ N3 y z E E E
del x (N2 y t1 t2)
  | x == y = case inorderSuc t2 of
    (v, SameD k) -> SameD $ N2 v t1 k
    (v, DiffD k) -> case t1 of
      N2 z t' t''        -> DiffD $ N3 z v t' t'' k
      N3 w z t' t'' t''' -> SameD $ N2 z (N2 w t' t'') (N2 v t''' k)
      _                  -> error "t1 cannot be empty here."
  | x < y = case del x t1 of
    SameD t' -> SameD $ N2 y t' t2
    DiffD t' -> case t2 of
      N2 a b c     -> DiffD $ N3 y a t' b c
      N3 a b c d e -> SameD $ N2 a (N2 y t' c) (N2 b d e)
      _            -> error "t2 cannot be empty here."
  | otherwise = case del x t2 of
    SameD t' -> SameD $ N2 y t1 t'
    DiffD t' -> case t1 of
      N2 a b c     -> DiffD $ N3 a y b c t'
      N3 a b c d e -> SameD $ N2 b (N2 a c d) (N2 y e t')
      _            -> error "t1 cannot be empty here."
del x (N3 y z t1 t2 t3)
  | x == y = case inorderSuc t2 of
    (v, SameD k) -> SameD $ N3 v z t1 k t3
    (v, DiffD k) -> case t1 of
      N2 w t' t''        -> SameD $ N2 z (N3 w v t' t'' k) t3
      N3 m w t' t'' t''' -> SameD $ N3 w z (N2 m t' t'') (N2 v t''' k) t3
      _                  -> error "t1 cannot be empty here."
  | x == z = case inorderSuc t3 of
    (v, SameD k) -> SameD $ N3 y v t1 t2 k
    (v, DiffD k) -> case t2 of
      N2 w t' t''        -> SameD $ N2 y t1 (N3 w v t' t'' k)
      N3 m w t' t'' t''' -> SameD $ N3 y w t1 (N2 m t' t'') (N2 v t''' k)
      _                  -> error "t2 cannot be empty here."
  | x < y = case del x t1 of
    SameD t' -> SameD $ N3 y z t' t2 t3
    DiffD t' -> case t2 of
      N2 a b c     -> SameD $ N2 z (N3 y a t' b c) t3
      N3 a b c d e -> SameD $ N3 a z (N2 y t' c) (N2 b d e) t3
      _            -> error "t2 cannot be empty here."
  | x > z = case del x t3 of
    SameD t' -> SameD $ N3 y z t1 t2 t'
    DiffD t' -> case t2 of
      N2 a b c     -> SameD $ N2 y t1 (N3 a z b c t')
      N3 a b c d e -> SameD $ N3 y b t1 (N2 a c d) (N2 z e t')
      _            -> error "t2 cannot be empty here."
  | otherwise = case del x t2 of
    SameD t' -> SameD $ N3 y z t1 t' t3
    DiffD t' -> case t1 of
      N2 a b c     -> SameD $ N2 z (N3 a y b c t') t3
      N3 a b c d e -> SameD $ N3 b z (N2 a c d) (N2 y e t') t3
      _            -> error "t1 cannot be empty here."

-- Gets the inorder successor of an element in a 2-3 tree
inorderSuc :: Ord a => Tree h a -> (a, IRD h a)
inorderSuc (N2 x E E) = (x, DiffD E)
inorderSuc (N3 x y E E E) = (x, SameD $ N2 y E E)
inorderSuc (N2 x t1 t2@(N2 y t' t'')) = case inorderSuc t1 of
  (v, SameD k) -> (v, SameD $ N2 x k t2)
  (v, DiffD k) -> (v, DiffD $ N3 x y k t' t'')
inorderSuc (N2 x t1 t2@(N3 y z t' t'' t''')) = case inorderSuc t1 of
  (v, SameD k) -> (v, SameD $ N2 x k t2)
  (v, DiffD k) -> (v, SameD $ N2 y (N2 x k t') (N2 z t'' t'''))
inorderSuc (N3 x y t1 t2@(N2 z t' t'') t3) = case inorderSuc t1 of
  (v, SameD k) -> (v, SameD $ N3 x y k t2 t3)
  (v, DiffD k) -> (v, SameD $ N2 y (N3 x z k t' t'') t3)
inorderSuc (N3 x y t1 t2@(N3 w z t' t'' t''') t3) = case inorderSuc t1 of
  (v, SameD k) -> (v, SameD $ N3 x y k t2 t3)
  (v, DiffD k) -> (v, SameD $ N3 w y (N2 x k t') (N2 z t'' t''') t3)
inorderSuc _ = error "Inorder sucessor called on invalid or empty tree."

-- Delete quickCheck properties:
prop_delete_spec1 :: TTT Int -> Bool
prop_delete_spec1 t = all (\x -> not (member x (delete x t))) (elements t)

prop_delete_spec2 :: TTT Int -> Bool
prop_delete_spec2 t = all (\(x,y) -> x == y || 
                                     (member y (delete x t))) allpairs where
  allpairs = [ (x,y) | x <- elements t, y <- elements t ]

prop_delete_spec3 :: TTT Int -> Int -> Property
prop_delete_spec3 t x = not (x `elem` elements t) ==> 
                        (elements (delete x t) == elements t)

prop_delete_bst :: TTT Int -> Bool
prop_delete_bst t = all (\x -> prop_BST (delete x t)) (elements t)

prop_delete_balanced :: TTT Int -> Bool
prop_delete_balanced t = all (\x -> prop_balanced (delete x t)) (elements t)

prop_delete1 :: TTT Int -> Bool
prop_delete1 t = all (\x -> prop_tree (delete x t)) (elements t)

-- Main method
main :: IO ()
main = do putStrLn "All children are empty or no children are empty:"
          quickCheck $ prop_tree
          putStrLn "BST property:"
          quickCheck $ prop_BST
          putStrLn "Tree is always balanced:"
          quickCheck $ prop_balanced
          putStrLn "Element not in tree after it is deleted:"
          quickCheck $ prop_delete_spec1
          putStrLn "Deleting x from tree does not remove y unless x == y:"
          quickCheck $ prop_delete_spec2
          putStrLn "Tree unchanged if element is not in the tree:"
          quickCheck $ prop_delete_spec3
          putStrLn "prop_tree holds after deletion:"
          quickCheck $ prop_delete1
          putStrLn "prop_BST holds after deletion:"
          quickCheck $ prop_delete_bst
          putStrLn "prop_balanced after deletion:"
          quickCheck $ prop_delete_balanced
