-- Lucas Pena
-- Tayler Mandel
-- 2-3 Trees

{-# LANGUAGE InstanceSigs, GADTs, DataKinds #-}

module TwoThree where

--import Persistent

import Control.Monad
import Test.QuickCheck hiding (elements)
import Data.Maybe as Maybe
import Data.List (sort, nub)

data TTT a = E | N2 a (TTT a) (TTT a) | N3 a a (TTT a) (TTT a) (TTT a)
  deriving (Eq, Show, Ord)
           
nodeNum :: TTT a -> Maybe Int
nodeNum E              = Nothing
nodeNum (N2 _ _ _)     = Just 2
nodeNum (N3 _ _ _ _ _) = Just 3

{- 
Invariants:
  1. Every non-leaf node is a 2-node (N2) or a 3-node (N3).
  2. A 2-node contains 1 data item and has 2 children.
  3. A 3-node contains 2 data items and has 3 children.
  4. All leaf nodes are at the same level.
  5. All data are kept in sorted order (BST invariant).
  6. Every leaf node will contain 1 or 2 fields.
-}

-- First invariant
prop_tree1 :: TTT Int -> Bool
prop_tree1 E = True
prop_tree1 x@(N2 _ t1 t2)      = 
  nodeNum x == Just 2 && prop_tree1 t1 && prop_tree1 t2
prop_tree1 x@(N3 _ _ t1 t2 t3) = 
  nodeNum x == Just 3 && prop_tree1 t1 && prop_tree1 t2 && prop_tree1 t3

-- Fourth invariant
prop_tree2 :: TTT Int -> Bool
prop_tree2 E                 = True
prop_tree2 (N2 _ E E)        = True
prop_tree2 (N2 _ E _)        = False
prop_tree2 (N2 _ _ E)        = False
prop_tree2 (N2 _ t1 t2)      = prop_tree2 t1 && prop_tree2 t2
prop_tree2 (N3 _ _ E E E)    = True
prop_tree2 (N3 _ _ E _ _)    = False
prop_tree2 (N3 _ _ _ E _)    = False
prop_tree2 (N3 _ _ _ _ E)    = False
prop_tree2 (N3 _ _ t1 t2 t3) = prop_tree2 t1 && prop_tree2 t2 && prop_tree2 t3

height :: TTT a -> Int
height E                 = 0
height (N2 _ t1 t2)      = 1 + max (height t1) (height t2)
height (N3 _ _ t1 t2 t3) = 1 + max (max (height t1) (height t2)) (height t3)

prop_balanced :: TTT Int -> Bool
prop_balanced E                 = True
prop_balanced (N2 _ t1 t2)      = height t1 == height t2
prop_balanced (N3 _ _ t1 t2 t3) = ht1 == height t2 && ht1 == height t3
  where ht1 = height t1

-- Fifth invariant
prop_BST :: TTT Int -> Bool
prop_BST t = nub (sort x) == x where x = elements t

-- QuickCheck
instance (Ord a, Arbitrary a) => Arbitrary (TTT a) where
  arbitrary = liftM (foldr insert empty) arbitrary

main :: IO ()
main = do quickCheck $ prop_tree1
          quickCheck $ prop_tree2
          quickCheck $ prop_BST
          
-- Implementation
empty :: TTT a
empty = E

elements :: TTT a -> [a]
elements E                 = []
elements (N2 x t1 t2)      = elements t1 ++ x : elements t2
elements (N3 x y t1 t2 t3) = elements t1 ++ x : elements t2 ++ y : elements t3

member :: Ord a => a -> TTT a -> Bool
member _ E = False
member x (N2 y t1 t2) | x == y    = True
                      | x < y     = member x t1
                      | otherwise = member x t2
member x (N3 y z t1 t2 t3) | x == y || x == z = True
                           | x < y            = member x t1
                           | x > z            = member x t3
                           | otherwise        = member x t2

insert :: Ord a => a -> TTT a -> TTT a
insert x E = N2 x E E
insert x t = case ins x t of
  Right t'          -> t'
  Left (t', v, t'') -> N2 v t' t''

ins :: Ord a => a -> TTT a -> Either (TTT a, a, TTT a) (TTT a)
ins x (N2 y E E) 
  | x == y    = Right $ N2 y E E
  | x < y     = Right $ N3 x y E E E
  | otherwise = Right $ N3 y x E E E
ins x (N3 y z E E E) 
  | x == y || x == z = Right $ N3 y z E E E
  | x < y            = Left $ (N2 x E E, y, N2 z E E)
  | x > z            = Left $ (N2 y E E, z, N2 x E E)
  | otherwise        = Left $ (N2 y E E, x, N2 z E E)
ins x (N2 y t1 t2) 
  | x == y = Right $ N2 y t1 t2
  | x < y = case ins x t1 of
     Right t'          -> Right $ N2 y t' t2
     Left (t', v, t'') -> Right $ N3 v y t' t'' t2
  | otherwise = case ins x t2 of
     Right t'          -> Right $ N2 y t1 t'
     Left (t', v, t'') -> Right $ N3 y v t1 t' t''
ins x (N3 y z t1 t2 t3) 
  | x == y || x == z = Right $ N3 y z t1 t2 t3
  | x < y = case ins x t1 of
     Right t' -> Right $ N3 y z t' t2 t3
     Left (t', v, t'') -> Left $ (N2 v t' t'', y, N2 z t2 t3)
  | x > z = case ins x t3 of
     Right t'          -> Right $ N3 y z t1 t2 t'
     Left (t', v, t'') -> Left $ (N2 y t1 t2, z, N2 v t' t'')
  | otherwise = case ins x t2 of
     Right t'          -> Right $ N3 y z t1 t' t3
     Left (t', v, t'') -> Left $ (N2 y t1 t', v, N2 z t'' t3)

delete :: Ord a => a -> TTT a -> TTT a
delete x E = E
delete x t = case del x t of
  Right t' -> t'
  Left t'  -> t'

del :: Ord a => a -> TTT a -> Either (TTT a) (TTT a)
del x (N2 y E E)
  | x == y = Left E
  | otherwise = Right $ N2 y E E
del x (N3 y z E E E)
  | x == y = Right $ N2 z E E
  | x == z = Right $ N2 y E E
  | otherwise = Right $ N3 y z E E E
del x (N2 y t1 t2)
  | x == y = case inorderSuc t2 of
     Right (v, k) -> Right $ N2 v t1 k
     Left (v, k)  -> case t1 of
       N2 z t' t''        -> Left $ N3 z v t' t'' k
       N3 w z t' t'' t''' -> Right $ N2 z (N2 w t' t'') (N2 v t''' k)
  | x < y = case del x t1 of
     Right t' -> Right $ N2 y t' t2
     Left t'  -> reb2Left y t' t2
  | otherwise = case del x t2 of
     Right t' -> Right $ N2 y t1 t'
     Left t'  -> reb2Right y t1 t'
del x (N3 y z t1 t2 t3)
  | x == y = case inorderSuc t2 of
     Right (v, k) -> Right $ N3 v z t1 k t3
     Left (v, k)  -> case t1 of
       N2 w t' t''        -> Right $ N2 z (N3 w v t' t'' k) t3
       N3 m w t' t'' t''' -> Right $ N3 w z (N2 m t' t'') (N2 v t''' k) t3
  | x == z = case inorderSuc t3 of
     Right (v, k) -> Right $ N3 y v t1 t2 k
     Left (v, k)  -> case t2 of
       N2 w t' t''        -> Right $ N2 y t1 (N3 w v t' t'' k)
       N3 m w t' t'' t''' -> Right $ N3 y w t1 (N2 m t' t'') (N2 v t''' k)
  | x < y = case del x t1 of
     Right t' -> Right $ N3 y z t' t2 t3
     Left t'  -> reb3Left y z t' t2 t3
  | x > z = case del x t3 of
     Right t' -> Right $ N3 y z t1 t2 t'
     Left t'  -> reb3Right y z t1 t2 t'
  | otherwise = case del x t2 of
     Right t' -> Right $ N3 y z t1 t' t3
     Left t'  -> reb3Middle y z t1 t' t3
     
inorderSuc :: Ord a => TTT a -> Either (a, TTT a) (a, TTT a)
inorderSuc E = error "Inorder successor called on empty tree."
inorderSuc (N2 x E E) = Left (x, E)
inorderSuc (N3 x y E E E) = Right (x, N2 y E E)
inorderSuc (N2 x t1 t2@(N2 y t' t'')) = case inorderSuc t1 of
  Right (v, k) -> Right (v, N2 x k t2)
  Left (v, k)  -> Left (v, N3 x y k t' t'')
inorderSuc (N2 x t1 t2@(N3 y z t' t'' t''')) = case inorderSuc t1 of
  Right (v, k) -> Right (v, N2 x k t2)
  Left (v, k)  -> Right (v, N2 y (N2 x k t') (N2 z t'' t'''))
inorderSuc (N3 x y t1 t2@(N2 z t' t'') t3) = case inorderSuc t1 of
  Right (v, k) -> Right (v, N3 x y k t2 t3)
  Left (v, k)  -> Right (v, N2 y (N3 x z k t' t'') t3)
inorderSuc (N3 x y t1 t2@(N3 w z t' t'' t''') t3) = case inorderSuc t1 of
  Right (v, k) -> Right (v, N3 x y k t2 t3)
  Left (v, k)  -> Right (v, N3 w y (N2 x k t') (N2 z t'' t''') t3)
  
reb2Left :: a -> TTT a -> TTT a -> Either (TTT a) (TTT a)
reb2Left v t1 (N2 x t' t'')        = Left $ N3 v x t1 t' t''
reb2Left v t1 (N3 x y t' t'' t''') = Right $ N2 x (N2 v t1 t') (N2 y t'' t''')
reb2Left _ _ _ = error "Invalid input to reb2Left."

reb2Right :: a -> TTT a -> TTT a -> Either (TTT a) (TTT a)
reb2Right v (N2 x t' t'') t2        = Left $ N3 x v t' t'' t2
reb2Right v (N3 x y t' t'' t''') t2 = Right $ N2 y (N2 x t' t'') (N2 v t''' t2)
reb2Right _ _ _ = error "Invalid input to reb2Right."

reb3Left :: a -> a -> TTT a -> TTT a -> TTT a -> Either (TTT a) (TTT a)
reb3Left v w t1 (N2 x t' t'') t3        = Right $ N2 w (N3 v x t1 t' t'') t3
reb3Left v w t1 (N3 x y t' t'' t''') t3 = 
  Right $ N3 x w (N2 v t1 t') (N2 y t'' t''') t3
reb3Left _ _ _ _ _ = error "Invalid input to reb3Left."

reb3Middle :: a -> a -> TTT a -> TTT a -> TTT a -> Either (TTT a) (TTT a)
reb3Middle v w (N2 x t' t'') t2 t3        = Right $ N2 w (N3 x v t' t'' t2) t3
reb3Middle v w (N3 x y t' t'' t''') t2 t3 =
  Right $ N3 y w (N2 x t' t'') (N2 v t''' t2) t3
reb3Middle _ _ _ _ _ = error "Invalid input to reb3Middle."

reb3Right :: a -> a -> TTT a -> TTT a -> TTT a -> Either (TTT a) (TTT a)
reb3Right v w t1 (N2 x t' t'') t3        = Right $ N2 v t1 (N3 x w t' t'' t3)
reb3Right v w t1 (N3 x y t' t'' t''') t3 = 
  Right $ N3 v y t1 (N2 x t' t'') (N2 w t''' t3)
reb3Right _ _ _ _ _ = error "Invalid input to reb3Right."


-- Delete quickCheck properties:
prop_delete_spec1 :: TTT Int -> Bool
prop_delete_spec1 t = all (\x -> not (member x (delete x t))) (elements t)

prop_delete_spec2 :: TTT Int -> Bool
prop_delete_spec2 t = all (\(x,y) -> x == y || (member y (delete x t))) allpairs where
  allpairs = [ (x,y) | x <- elements t, y <- elements t ]

prop_delete_spec3 :: TTT Int -> Int -> Property
prop_delete_spec3 t x = not (x `elem` elements t) ==> (delete x t == t)

prop_delete_bst :: TTT Int -> Bool
prop_delete_bst t = all (\x -> prop_BST (delete x t)) (elements t)

prop_delete_balanced :: TTT Int -> Bool
prop_delete_balanced t = all (\x -> prop_balanced (delete x t)) (elements t)

prop_delete1 :: TTT Int -> Bool
prop_delete1 t = all (\x -> prop_tree1 (delete x t)) (elements t)

prop_delete2 :: TTT Int -> Bool
prop_delete2 t = all (\x -> prop_tree2 (delete x t)) (elements t)
