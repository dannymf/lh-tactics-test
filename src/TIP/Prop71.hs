{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

module TIP.Prop71 where

import Data
import Proof
import Tactic.Core.Quote

{-@ reflect elemList @-}
elemList :: Eq a => a -> List a -> Bool
elemList x LNil = False
elemList x (LCons y ys) =
  if x == y
    then True
    else elemList x ys

{-@ reflect insertList @-}
insertList :: a -> List a -> List a
insertList n LNil = LCons n LNil
insertList n (LCons h t) = LCons n (LCons h t)

{-@ reflect lemma_prop @-}
lemma_prop x y ys = x == y || elemList x ys == elemList x ys

{-@
lemma :: x:a -> y:a -> ys:List a-> {lemma_prop x y ys}
@-}
lemma :: a -> a -> List a -> Proof
lemma x y ys = undefined

return []

{-@ reflect prop @-}
prop x y xs =
  x == y || elemList x (insertList y xs) == elemList x xs

{-@ automatic-instances proof @-}
{-@
proof :: x:N -> y:N -> xs:List N -> {prop x y xs}
@-}
-- [tactic|
-- proof :: N -> N -> List N -> Proof 
-- proof x y ys = 
--   condition {x == y};
--   induct ys as [/y' ys'];
--   [y']: condition {x == y'};
--   auto [lemma]
-- |]
-- %tactic:begin:proof
proof :: N -> N -> List N -> Proof
proof
  = \ x
      -> \ y
           -> \ ys
                -> if x == y then
                       case ys of
                         LNil -> trivial
                         LCons y' ys'
                           -> if x == y' then
                                  (((proof x) x) ys'
                                     &&&
                                       (((proof x) y) ys'
                                          &&& (((proof y) x) ys' &&& ((proof y) y) ys')))
                              else
                                  (((proof x) x) ys'
                                     &&&
                                       (((proof x) y) ys'
                                          &&& (((proof y) x) ys' &&& ((proof y) y) ys')))
                   else
                       case ys of
                         LNil -> trivial
                         LCons y' ys'
                           -> if x == y' then
                                  (((proof x) x) ys'
                                     &&&
                                       (((proof x) y) ys'
                                          &&& (((proof y) x) ys' &&& ((proof y) y) ys')))
                              else
                                  (((proof x) x) ys'
                                     &&&
                                       (((proof x) y) ys'
                                          &&& (((proof y) x) ys' &&& ((proof y) y) ys')))
-- %tactic:end:proof
-- %tactic:begin:proof

-- %tactic:begin:proof
-- proof :: N -> N -> List N -> Proof
-- proof = \x -> \y -> \ys -> if x == y
--                             then case ys of
--                                      Data.LNil -> trivial
--                                      Data.LCons y' ys' -> if x == y' then trivial else trivial
--                             else case ys of
--                                      Data.LNil -> trivial
--                                      Data.LCons y' ys' -> if x == y' then trivial else proof x y ys'
-- -- %tactic:end:proof
-- %tactic:end:proof
-- %tactic:begin:proof
-- TODO: not pruned

-- proof :: N -> N -> List N -> Proof
-- proof = \x -> \y -> \ys -> if x == y
--                             then case ys of
--                                      Data.LNil -> trivial
--                                      Data.LCons y' ys' -> if x == y' then trivial else trivial
--                             else case ys of
--                                      Data.LNil -> trivial
--                                      Data.LCons y' ys' -> if x == y' then trivial else proof x y ys'
