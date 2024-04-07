{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

module TIP.PropSimple where

import Data
import Proof
import Tactic.Core.Quote

{-@ reflect prop @-}
prop x y = (x == y) == not (x /= y)

{-@ automatic-instances proof @-}
{-@
proof :: x:N -> y:N -> {prop x y}
@-}
-- [tactic|
-- proof :: N -> N -> Proof
-- proof x y = auto []

-- | ]
--  %tactic:begin:proof
proof :: N -> N -> Proof
proof = \x -> \y -> trivial

-- %tactic:end:proof
