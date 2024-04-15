{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

-- {-@ LIQUID "--compile-spec" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

module TIP.Prop15 where

import Data
import Proof
import Tactic.Core.Quote

-- prop15_lemma

{-@ reflect prop15_lemma @-}
prop15_lemma :: N -> N -> ListN -> Bool
prop15_lemma n x l = lengthListN (insertListN n l) == lengthListN (Cons x l)

return []

{-@ automatic-instances prop15_lemma_proof @-}
{-@
prop15_lemma_proof :: n:N -> x:N -> l:ListN -> {prop15_lemma n x l}
@-}
-- [tactic|
-- prop15_lemma_proof :: N -> N -> ListN -> Proof
-- prop15_lemma_proof n x l =
--   induct l
-- |]
-- %tactic:begin:prop15_lemma_proof
prop15_lemma_proof :: N -> N -> ListN -> Proof
prop15_lemma_proof
  = \ n
      -> \ x
           -> \ l
                -> case l of
                     Nil -> trivial
                     Cons n_0 listN_1
                       -> (((prop15_lemma_proof n) n) listN_1
                             &&&
                               (((prop15_lemma_proof n) n_0) listN_1
                                  &&&
                                    (((prop15_lemma_proof n) x) listN_1
                                       &&&
                                         (((prop15_lemma_proof n_0) n) listN_1
                                            &&&
                                              (((prop15_lemma_proof n_0) n_0) listN_1
                                                 &&&
                                                   (((prop15_lemma_proof n_0) x) listN_1
                                                      &&&
                                                        (((prop15_lemma_proof x) n) listN_1
                                                           &&&
                                                             (((prop15_lemma_proof x) n_0)
                                                                listN_1
                                                                &&&
                                                                  ((prop15_lemma_proof x) x)
                                                                    listN_1))))))))
-- %tactic:end:prop15_lemma_proof
-- prop15

{-@ reflect prop15 @-}
prop15 :: N -> ListN -> Bool
prop15 n l = lengthListN (insertListN n l) == S (lengthListN l)

return []

{-@ automatic-instances prop15_proof @-}
{-@
prop15_proof :: n:N -> l:ListN -> {prop15 n l}
@-}
-- [tactic|
-- prop15_proof :: N -> ListN -> Proof
-- prop15_proof n l =
--   induct l;
--   auto [prop15_lemma_proof]
-- |]
-- %tactic:begin:prop15_proof
prop15_proof :: N -> ListN -> Proof
prop15_proof = \n -> \l -> case l of
                               Data.Nil -> trivial
                               Data.Cons n_0 listN_1 -> prop15_proof n listN_1
-- %tactic:end:prop15_proof

