{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

-- {-@ LIQUID "--compile-spec" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

module TIP.Prop26a where

import Data
import Proof
import Tactic.Core.Quote

-- prop26

{-@ reflect elemList @-}
elemList :: Eq a => a -> List a -> Bool
elemList x LNil = False
elemList x (LCons y ys) =
  if x == y
    then True
    else elemList x ys

{-@ reflect concatList @-}
concatList :: List a -> List a -> List a
concatList LNil l2 = l2
concatList (LCons h l1) l2 = LCons h (concatList l1 l2)

{-@ reflect prop26 @-}
prop26 :: Eq a => a -> List a -> List a -> Bool
prop26 x xs ys =
  implies
    (elemList x xs)
    (elemList x (concatList xs ys))

-- return []

-- {-@ automatic-instances prop26_proof @-}
-- {-@
-- prop26_proof :: x:a -> xs:List a -> ys:List a -> {prop26 x xs ys}
-- @-}
-- [tactic|
-- prop26_proof :: a -> List a -> List a -> Proof
-- prop26_proof x xs ys = induct xs
-- |]
-- %tactic:begin:prop26prop26_proof :: a -> List a -> List a -> Proof
-- prop26_proof = \x -> \xs -> \ys -> case xs of
--                                        Data.LNil -> trivial
--                                        Data.LCons x_0 x_1 -> prop26_proof x x_1 ys_proof
-- 
-- %tactic:end:prop26_proof

-- %tactic:begin:prop26_proof
-- prop26_proof :: a -> List a -> List a -> Proof
-- prop26_proof = \x -> \xs -> \ys -> case xs of
--                                        Data.LNil -> trivial
--                                        Data.LCons x_0 x_1 -> prop26_proof x x_1 ys
-- %tactic:end:prop26_proof
-- %tactic:begin:prop26_proof
-- %tactic:end:prop26_proof
