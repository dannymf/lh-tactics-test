{-# LANGUAGE QuasiQuotes #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module TIP.MonoidMaybe where

import Prelude hiding (mappend, mempty)
import Tactic.Core.Quote
import Proof

-- | Monoid
-- | mempty-left forall x . mappend mempty ? x == x
-- | mempty-right forall x . mappend x ? mempty == x
-- | mappend-assoc forall x y z . mappend (mappend x ? y) ?z == mappend x ?(mappend y ?z)

{-@ reflect mempty @-}
mempty :: Maybe a
mempty = Nothing


{-@ reflect mappend @-}
mappend :: Maybe a -> Maybe a -> Maybe a
mappend Nothing y
  = y
mappend (Just x) y
  = Just x

mempty_left :: Maybe a -> Proof
{-@ mempty_left :: x:Maybe a -> { mappend mempty x == x }  @-}
mempty_left _ = trivial 

{-@ mempty_right :: x:Maybe a -> { mappend x mempty == x }  @-}
-- [tactic| 
-- mempty_right :: Maybe a -> Proof
-- mempty_right x = destruct x
-- ]
-- 
-- {-@ 
-- mappend_assoc :: xs:Maybe a -> ys:Maybe a -> zs:Maybe a
--                   -> {mappend (mappend xs ys) zs == mappend xs (mappend ys zs) } 
-- @-}
-- [tactic| 
-- mappend_assoc :: Maybe a -> Maybe a -> Maybe a -> Proof
-- mappend_assoc xs ys zs = destruct xs; destruct ys
-- |]
-- %tactic:begin:mempty_right
mempty_right :: Maybe a -> Proof
mempty_right
  = \ x
      -> case x of
           Nothing -> trivial
           Just x_0 -> trivial
-- %tactic:end:mempty_right

{-@ 
mappend_assoc :: xs:Maybe a -> ys:Maybe a -> zs:Maybe a
                  -> {mappend (mappend xs ys) zs == mappend xs (mappend ys zs) } 
@-}
-- [tactic| 
-- mappend_assoc :: Maybe a -> Maybe a -> Maybe a -> Proof
-- mappend_assoc xs ys zs = destruct xs; destruct ys
-- |]
-- %tactic:begin:mappend_assoc
mappend_assoc :: Maybe a -> Maybe a -> Maybe a -> Proof
mappend_assoc
  = \ xs
      -> \ ys
           -> \ zs
                -> case xs of
                     Nothing
                       -> case ys of
                            Nothing -> trivial
                            Just x_0 -> trivial
                     Just x_0
                       -> case ys of
                            Nothing -> trivial
                            Just x_1 -> trivial
-- %tactic:end:mappend_assoc

-- mappend_assoc (Just x) y z
--   =   trivial
-- mappend_assoc Nothing (Just y) z
--   =   trivial
-- mappend_assoc Nothing Nothing z
--   =   trivial

