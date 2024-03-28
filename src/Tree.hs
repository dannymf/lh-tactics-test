{-@ LIQUID "--reflection" @-}
-- {-@ LIQUID "--compile-spec" @-}
{-@ LIQUID "--ple-local" @-}

module Tree where

import Proof
import Data hiding (TreeN(..))

{-@ data BST a b   = Leaf
                  | Node { key  :: a
                         , val :: Maybe b
                         , left  :: BSTL a b key
                         , right :: BSTR a b key } @-}
data BST a b = Leaf
           | Node { key  :: a
                  , val :: Maybe b
                  , left  :: BST a b
                  , right :: BST a b }

{-@ type BSTL a b X = BST {v:a | v < X} b           @-}
{-@ type BSTR a b X = BST {v:a | X < v} b         @-}

okBST :: BST Int Bool
okBST =  Node 6 Nothing 
             (Node 3 Nothing
                 (Node 1 Nothing Leaf Leaf)
                 (Node 4 Nothing Leaf Leaf))
             (Node 9 Nothing
                 (Node 7 Nothing Leaf Leaf)
                 Leaf)

-- badBST =  Node 66 
--              (Node 4
--                  (Node 1 Leaf Leaf)
--                  (Node 69 Leaf Leaf))  -- Out of order, rejected
--              (Node 99
--                  (Node 77 Leaf Leaf)
--                  Leaf)

{-@ reflect mem @-}
mem                 :: (Ord a) => a -> BST a b -> Bool
mem _ Leaf          = False
mem k (Node k' _ l r)
  | k == k'         = True
  | k <  k'         = mem k l
  | otherwise       = mem k r

{-@ reflect one @-}
one   :: a -> BST a b
one k = Node k Nothing Leaf Leaf

{-@ reflect add @-}
add                  :: (Ord a) => a -> Maybe b -> BST a b -> BST a b
add k' v' Leaf          = Node k' v' Leaf Leaf
add k' v' (Node k v l r)
  | k' < k           = Node k v (add k' v' l) r
  | k  < k'          = Node k v l (add k' v' r)
  | otherwise        = Node k v' l r

{-@ reflect size @-}
size :: (Ord a) => BST a b -> N
size Leaf = Z
size (Node _ _ l r) = S (addN (size l) (size r))

{-@ reflect prop1 @-}
prop1 :: N -> Bool 
prop1 n = mem n (one n)

{-@ automatic-instances proof1 @-}
{-@ proof1 :: n:N -> {prop1 n} @-}
proof1 :: N -> Proof 
proof1 n = trivial

{-@ automatic-instances prop3 @-}
{-@ prop3 :: n:N -> {size (one n) == S Z} @-}
prop3 :: N -> Proof
prop3 n = trivial

{-@ reflect prop2 @-}
prop2 :: Ord a => a -> BST a b -> Bool
prop2 x bst = mem x (add x Nothing bst)

{-@ automatic-instances proof2 @-}
{-@ proof2 :: Ord a => n:a -> bst:BST a b -> {prop2 n bst} @-}
proof2 :: Ord a => a -> BST a b -> Proof
proof2 n Leaf = trivial
proof2 n (Node root _ l r) = 
  case n `compare` root of
    EQ -> trivial
    LT -> proof2 n l 
    GT -> proof2 n r

{-@
lemma :: m:N -> n:N -> {addN m (S n) == S (addN m n)}
@-}
lemma :: N -> N -> Proof 
lemma m n = undefined

-- {-@ reflect prop4 @-}
-- prop4 :: Ord a => a -> BST a b -> Bool
-- prop4 a bst = size bst `leqN` size (add a Nothing bst)

-- {-@ automatic-instances proof4 @-}
-- {-@ proof4 :: Ord a => n:a -> bst:BST a b -> {prop4 n bst} @-}
-- proof4 :: Ord a => a -> BST a b -> Proof
-- proof4 a Leaf = trivial
-- proof4 a (Node root _ l r) = proof4 a l &&& proof4 a r


