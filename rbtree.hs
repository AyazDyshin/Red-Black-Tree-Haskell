
import Control.Monad
import Data.Time
import System.Random
{-
implementation of simple binary search tree
-}
data Tree a = Null1 | Node1 a (Tree a) (Tree a) deriving (Show, Read, Eq)

treeInsert :: Ord a => Tree a -> a -> Tree a
treeInsert Null1 x = Node1 x Null1 Null1
treeInsert (Node1 a left right) x
    | x == a = Node1 x left right
    | x < a  = Node1 a (treeInsert left x) right
    | x > a  = Node1 a left (treeInsert right x)

subDel :: Ord a => Tree a -> Tree a
subDel (Node1 a Null1 Null1) = Null1
subDel (Node1 a left Null1) = left
subDel (Node1 a Null1 right) = right
subDel (Node1 a left right) = Node1 val left (treeDelete right val)
   where val = inordSucc right

inordSucc :: Tree p -> p
inordSucc (Node1 a Null1 right) = a
inordSucc (Node1 a left right) = (inordSucc left)

treeDelete :: Ord a => Tree a -> a -> Tree a
treeDelete Null1 x = Null1
treeDelete (Node1 a left right) x
   |x < a = Node1 a (treeDelete left x) right
   |x > a = Node1 a left (treeDelete right x)
   |x == a = subDel (Node1 a left right)

{-function to print binary tree-}
printTree :: Show a => Tree a -> [Char]
printTree (Null1) = "Empty Tree"
printTree (Node1 value left right ) = unlines (subFunc (Node1 value left right))
   where
        p x xs = zipWith (++) (x : repeat xs)
        subTree left right = p "+- " "|  " (subFunc left) ++ p "`- " "   " (subFunc right)
        subFunc  Null1 = []
        subFunc (Node1 value left right) =  (show value) : subTree left right


{-start of RB tree implementation-}
data Color = Red | Black |BBlack deriving (Eq, Read)
instance Show Color where
   show Red = "R"
   show Black = "B"
   show BBlack = "BB"

data RBtree  = Null | Node Color Int (RBtree ) (RBtree) | BBNull deriving (Show, Read, Eq)

{-simple function to check if tree contains specific value-}
contains :: Int -> RBtree -> Bool
contains x (Null) = False
contains x (Node _ value left right)
   | x == value = True
   | x > value = contains x right
   | otherwise = contains x left

{-function that makes root node black-}
blackRoot :: RBtree -> RBtree
blackRoot (Null) = Null
blackRoot (BBNull) = Null
blackRoot (Node _ value left right) = Node Black value left right

{-the following method is used in rBinsert each time we are about to decend into our binary tree, it is needed because when we add a node its color is Red
this might violate one of the red-black tree's constrains that doesn't allow red nodes to have red child. So in case if we added a node and it's parent is black
than we are done as this doesn't violate any constraint of red-black tree.
So when we add a red node and create a red-red parent-child relationship we might get it in 4 different cases and each of them needs to be handeled∷
case1: Black node has left red child which has left red child
case 2: Black node which has left red child which has right red child
case 3: Black node which has right red child which has left red child
case 4: Black node which has right red child which has right red child
the reason the method works is because it is called each time we have our recursion call to decend into the tree, so it starts it's work from the bottom of the rBinsert
and even if result of it's call will be new red red relationship created higher in the tree it will be handeled by previous calls of this method until we reach root ( the fix for red root problem is described in
comments to rBinsert)
the following cases are additional cases to handle the redRed violition during deletion
case 5: blackBlack node with left red child that has red right child
case 6: blackBlack node with red right child which has red left child-}
redRedFixUp :: RBtree -> RBtree
redRedFixUp (Node Black value1 (Node Red value2 (Node Red value3 left3 right3) right2) right1) =
  Node Red value2 (Node Black value3 left3 right3) (Node Black value1 right2 right1) --case 1
redRedFixUp (Node Black value1 (Node Red value2 left2 (Node Red value3 left3 right3)) right1) =
   Node Red value3 (Node Black value2 left2 left3) (Node Black value1 right3 right1) -- case 2
redRedFixUp (Node Black value1 left1 (Node Red value2 (Node Red value3 left3 right3) right2)) =
   Node Red value3 (Node Black value1 left1 left3) (Node Black value2 right3 right2) -- case 3
redRedFixUp (Node Black value1 left1 (Node Red value2 left2 (Node Red value3 left3 right3))) =
   Node Red value2 (Node Black value1 left1 left2) (Node Black value3 left3 right3) -- case 4
redRedFixUp (Node BBlack value1 (Node Red value2 left2 (Node Red value3 left3 right3)) right1) =
   Node Black value3 (Node Black value2 left2 left3) (Node Black value1 right3 right1) -- case 5
redRedFixUp (Node BBlack value1 left1 (Node Red value2 (Node Red value3 left3 right3) right2) ) =
   Node Black value3 (Node Black value1 left1 left3) (Node Black value2 right3 right2) -- case 6
redRedFixUp (Node color value left right) = Node color value left right

{- the method is an insertion to red-black tree, implementation is very similar to insertion in standart binary tree
 with 2 exceptions : when we decend into the tree we call redRedFixUp (details on its implementation in comments before it)
 and after we are done we call method blackRoot, which simply changes color of the root of a given tree to black
 (we need this as we insert red nodes by default and even if we create a new tree with 0 nodes, the first node added (root) will be Red, so we fix this
 and as a consecuence of or redRedFixUp actions, we might get red root, so it fixes this as well-}
rBinsert :: RBtree -> Int -> RBtree
rBinsert t x = blackRoot (rBinsert' t)
  where  rBinsert'  Null = Node Red x Null Null
         rBinsert'  (Node color a left right)
            | x == a = Node color x left right
            | x < a = redRedFixUp (Node color a (rBinsert' left)  right)
            | x > a = redRedFixUp (Node color a left  (rBinsert' right))


{- the method describles the deletion from red-black tree, we first start with 2 simple cases where after deletion no property is violated (these cases are needed
when the node to delete doesn't have a successor):
case 1: red node with null children
case 2: black node with left subtree : Red node with null children and right subtree null
the next case that we handle is deleting a black node with null children, as deleting a black node affects the black-height property, to conserve the black height
we indroduced a new color which is BlackBlack ie double black, double black nodes are also handeled
case 3: black node with null childer
case 4: handles all the other cases, these cases might cause some violation of rb tree properties this is why we always call blackBlackFixUp to fix the BlackBlack node case
and redRed case that might occur
-}
rBdelete :: RBtree -> Int -> RBtree
rBdelete t x = blackRoot (rBdelete' t)
   where rBdelete'  Null = Null
         rBdelete' (Node Red value Null Null) -- case 1
            | x == value = Null
            | otherwise = Node Red value Null Null
         rBdelete'  (Node Black value1 (Node Red value2 Null Null) Null) --case 2
            | x < value1 = (Node Black value1 (rBdelete' (Node Red value2 Null Null)) Null)
            | x == value1 = Node Black value2 Null Null
            | otherwise = (Node Black value1 (Node Red value2 Null Null) Null)
         rBdelete'  (Node Black value1 Null Null) --case 3
            | x == value1 = BBNull
            | otherwise = (Node Black value1 Null Null)
         rBdelete'  (Node color value left right)
            | x < value = blackBlackFixUp (Node color value (rBdelete' left) right)
            | x > value = blackBlackFixUp (Node color value left (rBdelete' right))
            | x == value  =  let (val , tree) = (findInordSucc right)
                              in blackBlackFixUp (Node color val left tree)



{-this is a helper method. It's goal is to handel the doubleblack nodes. So we can ecounter the following cases of BlackBlack nodes(when we are fixing the blackblack case
as we are changing childer for some nodes this may also result into a redRed violation, this is why after each change we call a redRedfixUp function in order to fix this as well)
 case 1: red node with BlackBlack left child and black right child
 case 1.1: same as case 1 but instead of BlackBlack node we have blackblack null
 case 2: similar to case 1 but otherway round.
 case2.1: similar to case 2 but instead of BlackBlack node we have BlackBlack null
 case 3 : black node with blackblack left child and black right child. As it also may itroduce a redRed violation, but because the resulting tree still has double black node, we extend redRedFixUp to inculde this case (same goes for case 3.1,4,4.1)
 case 3.1: same as case 3 but with BBNull
 case 4 :same as case 3 but otherway round
 case 4.1 : same as case 4 but with BBNull
 case 5: black node with BlackBlack left child and red right child which has left black child
 case 5.1 : same as case 5 but with BBNull
 case 6 : same as case 5 but other way round
 case 6.1: same as case 6 but with BBNull
 -}
blackBlackFixUp :: RBtree -> RBtree
blackBlackFixUp (Node Red value1 (Node BBlack value2 left2 right2) (Node Black value3 left3 right3)) =
   redRedFixUp ((Node Black value3 (Node Red value1 (Node Black value2 left2 right2) left3 ) right3)) --case 1
blackBlackFixUp (Node Red value1 BBNull (Node black value2 left2 right2)) =
   redRedFixUp((Node Black value2 (Node Red value1 Null left2) right2)) -- case 1.1
blackBlackFixUp (Node Red value1 (Node Black value2 left2 right2) (Node BBlack value3 left3 right3)) =
   redRedFixUp(Node Black value2 left2 (Node Red value1 right2 (Node Black value3 left3 right3))) --case 2
blackBlackFixUp (Node Red value1 (Node Black value2 left2 right2) BBNull) =
   redRedFixUp (Node Black value2 left2 (Node Red value1 right2 Null)) -- case 2.1
blackBlackFixUp (Node Black value1 (Node BBlack value2 left2 right2) (Node Black value3 left3 right3)) =
   redRedFixUp(Node BBlack value3 (Node Red value1 (Node Black value2 left2 right2) left3) right3) --case 3
blackBlackFixUp (Node Black value1 BBNull (Node Black value2 left2 right2)) =
   redRedFixUp(Node BBlack value2 (Node Red value1 Null left2) right2) -- case 3.1
blackBlackFixUp (Node Black value1 (Node Black value2 left2 right2) (Node BBlack value3 left3 right3)) =
   redRedFixUp(Node BBlack value2 left2 (Node Red value1 right2 (Node Black value3 left3 right3))) --case 4
blackBlackFixUp (Node Black value1  (Node Black value2 left2 right2) BBNull) =
   redRedFixUp(Node BBlack value2 left2 (Node Red value1 right2 Null)) -- case 4.1
blackBlackFixUp (Node Black value1 (Node BBlack value2 left2 right2) (Node Red value3 (Node Black value4 left4 right4) right3)) =
   (Node Black value3 (redRedFixUp(Node Black value4 (Node Red value1 (Node Black value2 left2 right2) left4) right4)) right3) --case 5
blackBlackFixUp (Node Black value1 BBNull (Node Red value3 (Node Black value4 left4 right4) right3)) =
   (Node Black value3 (redRedFixUp(Node Black value4 (Node Red value1 Null left4) right4)) right3) --case 5.1
blackBlackFixUp (Node Black value1 (Node Red value2 left2 (Node Black value3 left3 right3)) (Node BBlack value4 left4 right4)) =
   (Node Black value2 left2 (redRedFixUp(Node Black value3 left3 (Node Red value1 right3 (Node Black value4 left4 right4))))) -- case 6
blackBlackFixUp (Node Black value1 (Node Red value2 left2 (Node Black value3 left3 right3)) BBNull) =
   (Node Black value2 left2 (redRedFixUp(Node Black value3 left3 (Node Red value1 right3 Null)))) -- case 6.1
blackBlackFixUp (Node color value left right) = Node color value left right

{-a helper functin to find an inorder successor-}
findInordSucc :: RBtree -> (Int, RBtree)
findInordSucc (Node Red value Null Null) = (value, Null)
findInordSucc (Node Black value Null Null) = (value, BBNull)
findInordSucc (Node Black value Null (Node Red value2 Null Null)) = (value, Node Black value2 Null Null)
findInordSucc (Node color value left right) = let (val, tree) = findInordSucc left
                                              in (val, blackBlackFixUp (Node color value tree right))

{-simple function to get the value in the root node -}
getRootValue :: RBtree -> Int
getRootValue (Node color value left right) = value

{-function that deletes all values from RB tree-}
deleteAllval :: RBtree -> RBtree
deleteAllval (Null) = Null
deleteAllval (Node color value left right) =
   deleteAllval(rBdelete (Node color value left right) (getRootValue (Node color value left right)))

{-function to print rb tree-}
printRBTree :: RBtree -> [Char]
printRBTree (Null) = "Empty Tree"
printRBTree (Node color value left right ) = unlines (subFunc (Node color value left right))
   where
        p x xs = zipWith (++) (x : repeat xs)
        subTree left right = p "+- " "|  " (subFunc left) ++ p "`- " "   " (subFunc right)
        subFunc  Null = []
        subFunc (Node color value left right) =  (show color) : (show value) : subTree left right

main = do
    putStrLn "data for RBtree:"
    forM_ (take 6 (iterate (*2) 1000)) (\n -> do
        start <- getCurrentTime
        let tree = foldl rBinsert Null [1 .. n]
            tree2 = foldl rBdelete tree [1 .. n]
        when (tree2 /= Null) (putStrLn "error: tree is not empty")
        stop <- getCurrentTime
        putStrLn (show n ++ ": " ++ show (diffUTCTime stop start))
        )
    putStrLn "data for binary tree"
    forM_ (take 6 (iterate (*2) 1000)) (\n -> do
        start <- getCurrentTime
        let tree3 = foldl treeInsert Null1 [1 .. n]
            tree4 = foldl treeDelete tree3 [1 .. n]
        when (tree4 /= Null1) (putStrLn "error: tree is not empty")
        stop <- getCurrentTime
        putStrLn (show n ++ ": " ++ show (diffUTCTime stop start))
        )
