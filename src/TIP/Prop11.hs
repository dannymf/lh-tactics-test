{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

module TIP.Prop11 where

import Data
import Proof
import Tactic.Core.Quote

{-@ reflect prop @-}
prop xs = dropListN Z xs == xs

{-@ automatic-instances proof @-}
{-@
proof :: xs:ListN -> {prop xs}
@-}
-- [tactic|
-- proof :: ListN -> Proof
-- proof xs = induct xs

-- | ]
--  %tactic:begin:proof
proof :: ListN -> Proof
proof = \xs -> case xs of
  Data.Nil -> trivial
  Data.Cons n_0 listN_1 -> trivial

-- %tactic:end:proof
-- %tactic:begin:proof

-- %tactic:end:proof
