{-@ LIQUID "--reflection" @-}

module Data where

import Proof

{-@ check :: b:{Bool | b} -> {b} @-}
check :: Bool -> Proof 
check b = trivial

-- (P => Q) <=> (P \/ -Q)
{-@ reflect implies @-}
implies :: Bool -> Bool -> Bool
implies p q = if p then q else True

{-@ 
posit :: b:Bool -> {b}
@-}
posit :: Bool -> Proof 
posit b = undefined

-- Function

{-@ reflect constant @-}
constant :: a -> b -> a 
constant a _ = a

-- N

{-@
data N = Z | S N
@-}
data N = Z | S N deriving (Eq, Show, Ord)

{-@ reflect n_to_int @-}
{-@ n_to_int :: n:N -> {x:Int | 0 <= x} @-}
n_to_int :: N -> Int 
n_to_int Z = 0
n_to_int (S n) = 1 + n_to_int n

{-@ reflect addN @-}
addN :: N -> N -> N
addN Z n = n
addN (S m) n = S (addN m n)

{-@ reflect subN @-}
subN :: N -> N -> N
subN Z n = Z
subN m Z = m
subN (S m) (S n) = subN m n

{-@ reflect leqN @-}
leqN :: N -> N -> Bool
leqN Z n = True
leqN (S m) Z = False
leqN (S m) (S n) = leqN m n

{-@ reflect geqN @-}
geqN :: N -> N -> Bool
geqN n Z = True
geqN Z (S m) = False
geqN (S m) (S n) = geqN m n

{-@ reflect leN @-}
leN :: N -> N -> Bool
leN Z Z = False
leN Z (S n) = True
leN m Z = False
leN (S m) (S n) = leN m n

{-@ reflect maxN @-}
maxN :: N -> N -> N
maxN Z n = n
maxN m Z = m
maxN (S m) (S n) = S (maxN m n)

{-@ reflect minN @-}
minN :: N -> N -> N 
minN Z n = Z
minN m Z = Z 
minN (S m) (S n) = S (minN m n)

-- ListN

{-@
data ListN = Nil | Cons N ListN
@-}
data ListN = Nil | Cons N ListN deriving (Eq, Show)

{-@
data List a = LNil | LCons a (List a)
@-}
data List a = LNil | LCons a (List a) deriving (Eq, Show)


{-@ reflect concatListN @-}
concatListN :: ListN -> ListN -> ListN
concatListN Nil l2 = l2
concatListN (Cons h l1) l2 = Cons h (concatListN l1 l2)

{-@ reflect takeListN @-}
takeListN :: N -> ListN -> ListN
takeListN _ Nil = Nil
takeListN Z _ = Nil
takeListN (S n) (Cons h l) = Cons h (takeListN n l)

{-@ reflect dropListN @-}
dropListN :: N -> ListN -> ListN
dropListN _ Nil = Nil
dropListN Z l = l
dropListN (S n) (Cons h l) = dropListN n l

-- dannymf
-- {-@ reflect dropList @-}
-- dropList :: N -> [a] -> [a]
-- dropList _ [] = []
-- dropList Z as = as
-- dropList (S n) (a:as) = dropList n as

{-@ reflect dropWhileListN @-}
dropWhileListN :: (N -> Bool) -> ListN -> ListN
dropWhileListN f Nil = Nil
dropWhileListN f (Cons x xs) =
  if f x then dropWhileListN f xs else Cons x xs

{-@ reflect takeWhileListN @-}
takeWhileListN :: (N -> Bool) -> ListN -> ListN
takeWhileListN f Nil = Nil
takeWhileListN f (Cons x xs) =
  if f x then Cons x (takeWhileListN f xs) else Nil

{-@ reflect countListN @-}
countListN :: N -> ListN -> N
countListN n Nil = Z
countListN n (Cons h l) = 
  if n == h then S (countListN n l) else countListN n l

{-@ reflect lengthListN @-}
lengthListN :: ListN -> N
lengthListN Nil = Z
lengthListN (Cons h t) = S (lengthListN t)

{-@ reflect lengthListN_int @-}
{-@ lengthListN_int :: ListN -> {x:Int | 0 <= x} @-}
lengthListN_int :: ListN -> Int 
lengthListN_int Nil = 0
lengthListN_int (Cons h t) = 1 + lengthListN_int t

{-@ reflect insertListN @-}
insertListN :: N -> ListN -> ListN
insertListN n Nil = Cons n Nil
insertListN n (Cons h t) =
  if leqN n h
    then Cons n (Cons h t)
    else Cons h (insertListN n t)

{-@ reflect sortListN @-}
sortListN :: ListN -> ListN
sortListN Nil = Nil
sortListN (Cons h t) = insertListN h (sortListN t)

{-@ reflect sortedListN @-}
sortedListN :: ListN -> Bool 
sortedListN Nil = True
sortedListN (Cons x Nil) = True 
sortedListN (Cons x1 xs'@(Cons x2 xs'')) = leqN x1 x2 && sortedListN xs'

{-@ reflect elemListN @-}
elemListN :: N -> ListN -> Bool
elemListN x Nil = False
elemListN x (Cons y ys) =
  if x == y
    then True
    else elemListN x ys

{-@ reflect initListN @-}
initListN :: ListN -> ListN
initListN Nil = Nil
initListN (Cons h Nil) = Nil
initListN (Cons h t) = Cons h (initListN t)

{-@ reflect singletonListN @-}
singletonListN :: N -> ListN 
singletonListN n = Cons n Nil

{-@ reflect ins1 @-}
ins1 :: N -> ListN -> ListN
ins1 n Nil = singletonListN n
ins1 n (Cons x xs) =
  if n == x 
    then Cons x xs
    else Cons x (ins1 n xs)

{-@ reflect lastListN @-}
lastListN :: N -> ListN -> N 
lastListN x Nil = x
lastListN x (Cons h t) = lastListN h t

{-@ reflect lastListN' @-}
lastListN' :: ListN -> N 
lastListN' Nil = Z
lastListN' (Cons x Nil) = x
lastListN' (Cons x xs) = lastListN' xs


{-@ reflect nullListN @-}
nullListN :: ListN -> Bool
nullListN Nil = True
nullListN _ = False

{-@ reflect initConcatListN @-}
initConcatListN :: ListN -> ListN -> ListN 
initConcatListN xs Nil = initListN xs 
initConcatListN xs (Cons y ys) = concatListN xs (initListN ys)

{-@ reflect reverseListN @-}
reverseListN :: ListN -> ListN
reverseListN Nil = Nil
reverseListN (Cons h t) = concatListN (reverseListN t) (singletonListN h)

{-@ reflect lastOfTwo @-}
lastOfTwo :: ListN -> ListN -> N
lastOfTwo xs Nil = lastListN' xs
lastOfTwo xs ys = lastListN' ys

{-@ reflect deleteListN @-}
deleteListN :: N -> ListN -> ListN
deleteListN x Nil = Nil
deleteListN x (Cons y ys) = if x == y then deleteListN x ys else Cons y (deleteListN x ys)

{-@
data ListN2 = Nil2 | Cons2 N N ListN2
@-}
data ListN2 = Nil2 | Cons2 N N ListN2 deriving (Eq)

{-@ reflect zipListN @-}
zipListN :: ListN -> ListN -> ListN2
zipListN Nil _ = Nil2
zipListN _ Nil = Nil2
zipListN (Cons x xs) (Cons y ys) = Cons2 x y (zipListN xs ys)

{-@ reflect zipConcatListN @-}
zipConcatListN :: N -> ListN -> ListN -> ListN2
zipConcatListN _ _ Nil = Nil2
zipConcatListN x xs (Cons y ys) = Cons2 x y (zipListN xs ys)

{-@ reflect dropListN2 @-}
dropListN2 :: N -> ListN2 -> ListN2
dropListN2 Z xs = xs
dropListN2 _ Nil2 = Nil2
dropListN2 (S n) (Cons2 x1 x2 xs) = dropListN2 n xs

{-@ reflect takeListN2 @-}
takeListN2 :: N -> ListN2 -> ListN2
takeListN2 Z _ = Nil2
takeListN2 _ Nil2 = Nil2
takeListN2 (S n) (Cons2 x1 x2 xs) = Cons2 x1 x2 (takeListN2 n xs)

{-@ reflect concatListN2 @-}
concatListN2 :: ListN2 -> ListN2 -> ListN2 
concatListN2 Nil2 ys = ys
concatListN2 (Cons2 x1 x2 xs) ys = Cons2 x1 x2 (concatListN2 xs ys)

{-@ reflect singletonListN2 @-}
singletonListN2 :: N -> N -> ListN2 
singletonListN2 x1 x2 = Cons2 x1 x2 Nil2

{-@ reflect reverseListN2 @-}
reverseListN2 :: ListN2 -> ListN2
reverseListN2 Nil2 = Nil2
reverseListN2 (Cons2 x1 x2 xs) = concatListN2 (reverseListN2 xs) (singletonListN2 x1 x2)

-- TreeN

{-@
data TreeN = Leaf | Node N TreeN TreeN
@-}
data TreeN = Leaf | Node N TreeN TreeN deriving (Eq)

{-@ reflect heightTreeN @-}
heightTreeN :: TreeN -> N
heightTreeN Leaf = Z
heightTreeN (Node x l r) = S (maxN (heightTreeN l) (heightTreeN r))

{-@ reflect mirrorTreeN @-}
mirrorTreeN :: TreeN -> TreeN
mirrorTreeN Leaf = Leaf 
mirrorTreeN (Node x l r) = Node x (mirrorTreeN r) (mirrorTreeN l)