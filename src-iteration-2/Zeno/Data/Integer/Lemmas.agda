{-# OPTIONS --without-K --safe #-}

module Zeno.Data.Integer.Lemmas where

open import Algebra.Structures
open import Data.Integer
open import Data.Integer.Properties
open import Data.Integer.Solver
open import Relation.Binary.PropositionalEquality

lemma-1 : (a b c d : ℤ) → (c * b + (- a) * d) ≡ c * b - a * d
lemma-1 = solve 4 (λ a b c d → (c :* b :+ (:- a) :* d)
                            := c :* b :- a :* d) refl
  where open +-*-Solver

lemma-2 : (a b c d : ℤ) → (c * b + (- a) * d) * 1ℤ ≡ c * b - a * d
lemma-2 a b c d = begin
  (c * b + (- a) * d) * + 1 ≡⟨ *-identityʳ (c * b + (- a) * d) ⟩
  (c * b + (- a) * d)       ≡⟨ lemma-1 a b c d ⟩
  c * b - a * d             ∎
  where open ≡-Reasoning

*-1-isAbelianGroup : IsAbelianGroup _≡_ _*_ 0ℤ (-_)
*-1-isAbelianGroup = record { isGroup = {!*-1-isGroup!} ; comm = {!!} }

open import Zeno.Class.AbelianGroup {!!} public
