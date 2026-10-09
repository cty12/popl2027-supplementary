module LambdaAlphaRefStar.Theories.CoercionEquationalTheory.Definitions where

open import LambdaAlphaRefStar.Theories.CoercionEquationalTheory.EC.SyntaxAndTyping  public
open import LambdaAlphaRefStar.Theories.CoercionEquationalTheory.Code.SyntaxAndTyping public
open import LambdaAlphaRefStar.Theories.CoercionEquationalTheory.Meta.SyntaxAndTyping public
open import LambdaAlphaRefStar.Theories.CoercionEquationalTheory.EC.Semantics          public
open import LambdaAlphaRefStar.Theories.CoercionEquationalTheory.Code.Semantics        public
open import LambdaAlphaRefStar.Theories.CoercionEquationalTheory.Meta.Semantics        public

data IsProj : MCoercion → Set where
  proj : ∀ {G ℓ} → (g : Ground G) → IsProj ((G ？ ℓ) g)

data IsErr : MCoercion → Set where
  error : ∀ {ℓ} → IsErr (⊥ ℓ)
