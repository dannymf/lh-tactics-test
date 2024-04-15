{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}
{- LIQUID "--betaequivalence"  @-}
{-# LANGUAGE QuasiQuotes #-}

module TIP.MonadList where

import Prelude hiding (return, (>>=))

import Tactic.Core.Quote
import Proof
import TIP.FFF

-- | Monad Laws :
-- | Left identity:   return a >>= f  == f a
-- | Right identity:   m >>= return    == m
-- | Associativity:   (m >>= f) >>= g == m >>= (\x -> f x >>= g)
-- imported from Append
prop_append_neutral :: L a -> Proof
{-@ assume prop_append_neutral :: xs:L a -> { append xs N == xs }  @-}
prop_append_neutral N
  = trivial
prop_append_neutral (C x xs)
  = prop_append_neutral xs

{-@
prop_assoc :: xs:L a -> ys:L a -> zs:L a
               -> { append (append xs ys) zs == append xs (append ys zs) } 
@-}
[tactic| 
prop_assoc :: L a -> L a -> L a -> Proof
prop_assoc xs ys zs = induct xs
|]
-- prop_assoc N ys zs
--   =  trivial

-- prop_assoc (C x xs) ys zs
--   =   prop_assoc xs ys zs

{-@ reflect return @-}
return :: a -> L a
return x = C x N

{-@ reflect bind @-}
bind :: L a -> (a -> L b) -> L b
bind N f = N
bind (C x xs) f = append (f x) (bind xs f)

-- pure []

{-@ reflect append @-}
append :: L a -> L a -> L a
append N ys = ys
append (C x xs) ys = C x (append xs ys)

-- | Left Identity
{-@ left_identity :: x:a -> f:(a -> L b) -> { bind (return x) f == f x } @-}
-- [tactic|
-- left_identity :: a -> (a -> L b) -> Proof
-- left_identity x f = auto [prop_append_neutral]
-- |]
-- %tactic:begin:left_identity
left_identity :: a -> (a -> L b) -> Proof
left_identity = \ x -> \ f -> trivial
-- %tactic:end:left_identity


-- left_identity x f
--   =  prop_append_neutral (f x)


-- | Right Identity

{-@ right_identity :: x:L a -> { bind x return == x } @-}
-- [tactic| 
-- right_identity :: L a -> Proof
-- right_identity x = induct x
-- |]
-- %tactic:begin:right_identity
right_identity :: L a -> Proof
right_identity
  = \ x
      -> case x of
           N -> trivial
           C x_0 x_1 -> right_identity x_1
-- %tactic:end:right_identity

-- | Associativity:  (m >>= f) >>= g == m >>= (\x -> f x >>= g)

{-@ assume associativity :: m:L a -> f: (a -> L b) -> g:(b -> L c)
      -> {bind (bind m f) g == bind m (\x:a -> (bind (f x) g)) } @-}
associativity :: L a -> (a -> L b) -> (b -> L c) -> Proof
associativity N f g
  = trivial

associativity (C x xs) f g
  =   bind_append (f x) (bind xs f) g
  &&& associativity xs f g


bind_append :: L a -> L a -> (a -> L b) -> Proof
{-@ bind_append :: xs:L a -> ys:L a -> f:(a -> L b)
     -> { bind (append xs ys) f == append (bind xs f) (bind ys f) }
  @-}

bind_append N ys f
  =  trivial
bind_append (C x  xs) ys f
  =   bind_append xs ys f
  &&& prop_assoc (f x) (bind xs f) (bind ys f)
