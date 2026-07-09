module Theories.CoercionEquationalTheory.Definitions where

open import Theories.CoercionEquationalTheory.EC.SyntaxAndTyping  public
open import Theories.CoercionEquationalTheory.Code.SyntaxAndTyping public
open import Theories.CoercionEquationalTheory.Meta.SyntaxAndTyping public
open import Theories.CoercionEquationalTheory.EC.Semantics          public
open import Theories.CoercionEquationalTheory.Code.Semantics        public
open import Theories.CoercionEquationalTheory.Meta.Semantics        public

data IsProj : MCoercion → Set where
  proj : ∀ {G ℓ} → (g : Ground G) → IsProj ((G ？ ℓ) g)

data IsErr : MCoercion → Set where
  error : ∀ {ℓ} → IsErr (⊥ ℓ)
