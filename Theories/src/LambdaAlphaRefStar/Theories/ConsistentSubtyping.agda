module LambdaAlphaRefStar.Theories.ConsistentSubtyping where

open import LambdaAlphaRefStar.Theories.EnvClassifiers
open import LambdaAlphaRefStar.Theories.CodeTypes
open import LambdaAlphaRefStar.Theories.MetaTypes

{-
  Consistent subtyping is used in the type system of the surface language.
  During elaboration, this implicit conversion between types is made explicit
  as casts (or coercions) through the "coerce" functions.
-}

infix 4 _⊢_≲_
infix 4 _≲ᵒ_
infix 4 _⊢ᵉ_≲_

data _⊢ᵉ_≲_ (Θ : SubCtx) : EC⋆ → EC⋆ → Set where

  csubᵉ-⋆-left : ∀ {ê}
      ------------------ (⋆≲)
    → Θ ⊢ᵉ ⋆ ≲ ê

  csubᵉ-⋆-right : ∀ {ê}
      ------------------ (≲⋆)
    → Θ ⊢ᵉ ê ≲ ⋆

  csubᵉ-ec : ∀ {e e′}
    → Θ ⊢ᵉ e <: e′
      --------------------- (≲-ec-sub)
    → Θ ⊢ᵉ ec e ≲ ec e′


data _≲ᵒ_ : OType⋆ → OType⋆ → Set where

  csubᵒ-⋆-left : ∀ {O}
      ------------------ (⋆≲)
    → ⋆ ≲ᵒ O

  csubᵒ-⋆-right : ∀ {O}
      --------------------- (≲⋆)
    → O ≲ᵒ ⋆

  csubᵒ-base : ∀ {ι}
      --------------------- (≲-base)
    → ` ι ≲ᵒ ` ι

  csubᵒ-fun : ∀ {A A′ B B′}
    → A′ ≲ᵒ A
    → B  ≲ᵒ B′
      ------------------------------ (≲-fun)
    → (A ⇒ B) ≲ᵒ (A′ ⇒ B′)


data _⊢_≲_ (Θ : SubCtx) : MType → MType → Set where

  csub-⋆-left : ∀ {A}
      ------------------ (⋆≲)
    → Θ ⊢ ⋆ ≲ A

  csub-⋆-right : ∀ {A}
      ------------------ (≲⋆)
    → Θ ⊢ A ≲ ⋆

  csub-base : ∀ {ι}
      ------------------ (≲-base)
    → Θ ⊢ ` ι ≲ ` ι

  csub-fun : ∀ {A A′ B B′}
    → Θ ⊢ A′ ≲ A
    → Θ ⊢ B  ≲ B′
      --------------------------------- (≲-fun)
    → Θ ⊢ (A ⇒ B) ≲ (A′ ⇒ B′)

  csub-ref : ∀ {A B}
    → Θ ⊢ A ≲ B
    → Θ ⊢ B ≲ A
      --------------------------- (≲-ref)
    → Θ ⊢ Ref A ≲ Ref B

  csub-code : ∀ {O O′ ê ê′}
    →      O ≲ᵒ O′
    → Θ ⊢ᵉ ê ≲ ê′
      --------------------------- (≲-code)
    → Θ ⊢ ‶ O ″ ê ≲ ‶ O′ ″ ê′

  csub-univ : ∀ {A B}
    → ⇑ᵉ-subctx Θ ⊢ A ≲ B
      --------------------------- (≲-univ)
    → Θ ⊢ ∀̇ A ≲ ∀̇ B

  csub-sub : ∀ {e₁ e₂ A B}
    → (Θ , e₁ <: e₂) ⊢ A ≲ B
      ------------------------------------------ (≲-sub)
    → Θ ⊢ (e₁ <: e₂ => A) ≲ (e₁ <: e₂ => B)
