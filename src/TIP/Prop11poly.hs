{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

module TIP.Prop11poly where

import Data
import Data.Foldable (Foldable (foldl'))
import Proof
import Tactic.Core.Quote

{-@ reflect dropList @-}
dropList :: N -> List a -> List a
dropList _ LNil = LNil
dropList Z as = as
dropList (S n) (LCons a as) = dropList n as

{-@ reflect prop @-}
prop :: List Bool -> Bool
prop xs = dropList Z xs == xs

{-@ automatic-instances proof @-}
{-@
proof :: xs:List Bool -> {prop xs}
@-}
-- [tactic|
-- proof :: List Bool -> Proof
-- proof xs = induct xs
-- |]
-- %tactic:begin:proof
proof :: List Bool -> Proof
proof
  = \ xs
      -> case xs of
           LNil -> trivial
           LCons x_0 x_1 -> trivial
-- %tactic:end:proof
-- %tactic:begin:proof

-- %tactic:end:proof
--  %tactic:begin:proof
-- proof :: List Bool -> Proof
-- proof =
--   \xs ->
--     case xs of
--       LNil -> trivial
--       LCons x_0 x_1 -> trivial

-- %tactic:end:proof
