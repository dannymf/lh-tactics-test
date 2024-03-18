{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

module TIP.Prop52 where

import Data
import Proof
import Tactic.Core.Quote

{-@ reflect singletonList @-}
singletonList :: a -> List a
singletonList n = LCons n LNil

{-@ reflect reverseList @-}
reverseList :: List a -> List a
reverseList LNil = LNil
reverseList (LCons h t) = concatList (reverseList t) (singletonList h)

{-@ reflect concatList @-}
concatList :: List a -> List a -> List a
concatList LNil l2 = l2
concatList (LCons h l1) l2 = LCons h (concatList l1 l2)

{-@ reflect countList @-}
countList :: Eq a => a -> List a -> N
countList n LNil = Z
countList n (LCons h l) =
  if n == h then S (countList n l) else countList n l

{-@ automatic-instances lemma @-}
{-@
lemma :: n:a -> xs:List a -> ys:List a -> {countList n (concatList xs ys) == countList n (concatList ys xs)}
@-}
lemma :: Eq a => a -> List a -> List a -> Proof
lemma n xs ys = undefined

return []

-- * takes 3m47s to prune

{-@ automatic-instances proof @-}
{-@
proof :: n:a -> xs:List a -> {countList n xs == countList n (reverseList xs)}
@-}
-- [tactic|
-- proof :: N -> List N -> Proof
-- proof n xs =
--   induct xs;
--   auto [lemma, reverseList, singletonList] 3

-- | ]
--  %tactic:begin:proof
proof :: N -> List N -> Proof
proof =
  \n ->
    \xs ->
      case xs of
        LNil -> trivial
        LCons x_0 x_1 -> (proof n) x_1

-- %tactic:end:proof
