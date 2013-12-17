GADT 2-3 Trees
===

###Authors
Tate Mandel (tmandel)    
Lucas Pena (lpena)

###Files

#####`TwoThree1.hs`:
 - The first step in the project's development is housed in `TwoThree1.hs`.
   This file contains an implementation of 2-3 trees with no use of GADTs
   to verify the invariants. The file contains quickCheck properties to
   check the invariants of the 2-3 tree structure.

#####`TwoThree2.hs`:
 - The second step in the project's development is located in `TwoThree2.hs`.
   This file contains a version of the implementation in `TwoThree1.hs` 
   without deletion. This file uses GADTs to verify the properties of this
   implementation of 2-3 trees without deletion.

#####`Main.hs`:
 - The final product is held in `Main.hs` in its entirety. This is
   a full implementation of 2-3 trees with insertion, membership testing,
   listing of elements, and deletion using GADTs to verify the properties
   of the tree structure.

#####`Profiling` (directory):
 - `RedBlack.lhs`: Red Black Tree implementation as done in class.
 - `Persistent.lhs`: Module needed to compile RedBlack.lhs.
 - `TwoThree.hs`: Same as `Main.hs` without the main method.
 - `Profiling.hs`: Used to compare our implementation of 2-3 Trees with the
    implementation of Red Black Trees as done in class. Many elements are inserted
    and then deleted from each type of tree, and profiling is used to compare the
    speed of each implementation.

###Running/Compiling (Main):
The `Main.hs` file can be compiled by running `ghc --make Main.hs`. This 
assumes an appropriate version of GHC and the Haskell Platform suitable
for the use of GADTs. GHC version 7.6.3 is a known working version.

###Running/Compiling (Profiling):
In the `Profiling` directory, compile and run as follows:
`% ghc -O2 --make concurrency.lhs -prof -auto-all -caf-all -fforce-recomp -rtsopts`  
`% ./Profiling +RTS -p`  
Then, navigate to `Profiling.prof` to view the output.

###Testing
The GADT 2-3 trees are tested through use of QuickCheck. The following
properties were written and passed:

#####`prop_tree`:
 - All 2-nodes have two populated children and all 3-nodes have three 
   populated children. It is never the case that a node has one non-empty 
   child and one empty child.

#####`prop_balanced`:
 - All children of a node have the same height.

#####`prop_BST`:
 - The elements of the tree are sorted by some natural ordering.

#####`prop_delete_spec1`:
 - After deleting an element from a tree, that element is not still present in the tree.

#####`prop_delete_spec2`:
 - Given two elements in a tree, x and y, deleting x from the tree will not 
remove y unless it is the case that x is equivalent to y. 

#####`prop_delete_spec3`:
 - If x is not a member of tree t, calling `delete x t` will not change the 
elements of the tree.

#####`prop_delete`:
 - The `prop_tree` property still holds after deleting an element from a 
   tree.

#####`prop_delete_BST`:
 - The `prop_BST` property still holds after deleting an element from a tree.

#####`prop_delete_balanced`:
 - The `prop_balanced` property still holds after deleting an element from 
   a tree.

###Possible Extensions
 - A simple use case
 - Refactored delete to reduce redundancy
 - More in-depth profiling between Red Black Trees and 2-3 Trees.
