module LambdaAlphaRefStar.Theories.Elaboration where

open import Data.Product renaming (_,_ to ⟨_,_⟩)

open import Utils
open import LambdaAlphaRefStar.Theories.SurfaceSyntaxAndTypeSystem
open import LambdaAlphaRefStar.Theories.ConsistentSubtyping public
open import LambdaAlphaRefStar.Theories.Coerce
open import LambdaAlphaRefStar.Theories.CCAlphaRefStarSyntaxAndTypeSystem


-- | LATER: Turn these compilation relations into functions
infix 3 _;_;_;_;_⊢_↝_⭆_
infix 3 _;_;_;_;_⊢_↝_⭅_
infix 3 _;_;_;_⊢_↝_⦂_

data _;_;_;_;_⊢_↝_⭆_ Δ Θ Γᵐ Γᵒ e : CodeSurfaceTerm → CodeTerm → OType → Set

data _;_;_;_;_⊢_↝_⭅_ Δ Θ Γᵐ Γᵒ e : CodeSurfaceTerm → CodeTerm → OType → Set

data _;_;_;_⊢_↝_⦂_ Δ Θ Γᵐ Γᵒ : MetaSurfaceTerm → MetaTerm → MType → Set


data _;_;_;_;_⊢_↝_⭆_ Δ Θ Γᵐ Γᵒ e where

  code-const : ∀ {ι} {k : base-rep ι}
      ---------------------------------------------
    → Δ ; Θ ; Γᵐ ; Γᵒ ; e ⊢ $ k ↝ $ k ⭆ ` ι

  code-var : ∀ {x T α}
    → Γᵒ ∋ᵒ x ⦂ ⟨ T , α ⟩
    → Θ ⊢ᵉ ` α <: e
      ---------------------------------------------
    → Δ ; Θ ; Γᵐ ; Γᵒ ; e ⊢ ` x ↝ ` x ⭆ T

  code-abs : ∀ {T₁ T₂ N N′}
    → let Θ′ = ⇑ᵉ-subctx Θ , ⇑ᵉ-ec e <: ` zero in
       let Γᵐ′ = ⇑ᵉ-mctx Γᵐ in
       let Γᵒ′ = ⇑ᵉ-octx Γᵒ , T₁ ＠ zero in
       Δ ,α ; Θ′ ; Γᵐ′ ; Γᵒ′ ; ` zero ⊢ N ↝ N′ ⭆ T₂
      ------------------------------------------------------------
    → Δ ; Θ ; Γᵐ ; Γᵒ ; e ⊢ ƛ T₁ ˙ N ↝ ƛ T₁ ˙ N′ ⭆ T₁ ⇒ T₂

  code-app : ∀ {T₁ T₂ L M L′ M′ ℓ}
    → Δ ; Θ ; Γᵐ ; Γᵒ ; e ⊢ L ↝ L′ ⭆ T₁ ⇒ T₂
    → Δ ; Θ ; Γᵐ ; Γᵒ ; e ⊢ M ↝ M′ ⭅ T₁
      ------------------------------------------------------
    → Δ ; Θ ; Γᵐ ; Γᵒ ; e ⊢ L · M ^ ℓ ↝ L′ · M′ ⭆ T₂


data _;_;_;_;_⊢_↝_⭅_ Δ Θ Γᵐ Γᵒ e where

  splice : ∀ {T O A M M′ ℓ}
    → Δ ; Θ ; Γᵐ ; Γᵒ ⊢ M ↝ M′ ⦂ A
    → (A≲T : Θ ⊢ A ≲ ‶ O ″ ec e)
    → O ↪ᵒ T
      ------------------------------------------------------------------
    → Δ ; Θ ; Γᵐ ; Γᵒ ; e ⊢ ~ M ^ ℓ ↝ ~ (M′ ⟨ coerceᵐ A≲T ℓ ⟩) ⭅ T

  check : ∀ {T M M′}
    → Δ ; Θ ; Γᵐ ; Γᵒ ; e ⊢ M ↝ M′ ⭆ T
      ---------------------------------------
    → Δ ; Θ ; Γᵐ ; Γᵒ ; e ⊢ M ↝ M′ ⭅ T


data _;_;_;_⊢_↝_⦂_ Δ Θ Γᵐ Γᵒ where

  meta-const : ∀ {ι} {k : base-rep ι}
      ---------------------------------------
    → Δ ; Θ ; Γᵐ ; Γᵒ ⊢ $ k ↝ $ k ⦂ ` ι

  meta-var : ∀ {x A}
    → Γᵐ ∋ x ⦂ A
      ---------------------------------------
    → Δ ; Θ ; Γᵐ ; Γᵒ ⊢ ` x ↝ ` x ⦂ A

  meta-abs : ∀ {A B M M′}
    → Δ ⊢ᵐᵗ A
    → Δ ; Θ ; (Γᵐ ⸴ A) ; Γᵒ ⊢ M ↝ M′ ⦂ B
      ------------------------------------------------
    → Δ ; Θ ; Γᵐ ; Γᵒ ⊢ ƛ A ˙ M ↝ ƛ M′ ⦂ A ⇒ B

  meta-app : ∀ {A₁ A₂ B L M L′ M′ ℓ}
    → Δ ; Θ ; Γᵐ ; Γᵒ ⊢ L ↝ L′ ⦂ A₁ ⇒ A₂
    → Δ ; Θ ; Γᵐ ; Γᵒ ⊢ M ↝ M′ ⦂ B
    → (B≲A₁ : Θ ⊢ B ≲ A₁)
      ---------------------------------------------------------------------
    → Δ ; Θ ; Γᵐ ; Γᵒ ⊢ L · M ^ ℓ ↝ L′ · (M′ ⟨ coerceᵐ B≲A₁ ℓ ⟩) ⦂ A₂

  meta-app⋆ : ∀ {A L M L′ M′ ℓ}
    → Δ ; Θ ; Γᵐ ; Γᵒ ⊢ L ↝ L′ ⦂ ⋆
    → Δ ; Θ ; Γᵐ ; Γᵒ ⊢ M ↝ M′ ⦂ A
      ------------------------------------------------------------------------
    → let ⋆⇒⋆→⋆ = coerceᵐ (csub-⋆-left {Θ} {⋆ ⇒ ⋆}) ℓ in
       let    A⇒⋆ = coerceᵐ (csub-⋆-right {Θ} {A}) ℓ in
       Δ ; Θ ; Γᵐ ; Γᵒ ⊢ L · M ^ ℓ ↝ (L′ ⟨ ⋆⇒⋆→⋆ ⟩) · (M′ ⟨ A⇒⋆ ⟩) ⦂ ⋆

  meta-ecabs : ∀ {A M M′}
    → Δ ,α ; ⇑ᵉ-subctx Θ ; ⇑ᵉ-mctx Γᵐ ; ⇑ᵉ-octx Γᵒ ⊢ M ↝ M′ ⦂ A
      ------------------------------------------------------------------
    → Δ ; Θ ; Γᵐ ; Γᵒ ⊢ Λ M ↝ Λ M′ ⦂ ∀̇ A

  meta-ecapp : ∀ {A M M′ e ℓ}
    → Δ ⊢ᵉ e
    → Δ ; Θ ; Γᵐ ; Γᵒ ⊢ M ↝ M′ ⦂ ∀̇ A
      ------------------------------------------------------------
    → Δ ; Θ ; Γᵐ ; Γᵒ ⊢ M ·[ e ]^ ℓ ↝ M′ ·[ e ] ⦂ A [ e ]ᵉ

  meta-ecapp⋆ : ∀ {M M′ e ℓ}
    → Δ ⊢ᵉ e
    → Δ ; Θ ; Γᵐ ; Γᵒ ⊢ M ↝ M′ ⦂ ⋆
      ------------------------------------------------------------------
    → let ⋆⇒∀⋆ = coerceᵐ (csub-⋆-left {Θ} {∀̇ ⋆}) ℓ in
       Δ ; Θ ; Γᵐ ; Γᵒ ⊢ M ·[ e ]^ ℓ ↝ (M′ ⟨ ⋆⇒∀⋆ ⟩) ·[ e ] ⦂ ⋆

  meta-subintro : ∀ {A e₁ e₂ M M′}
    → Δ ⊢ᵉ e₁
    → Δ ⊢ᵉ e₂
    → Δ ; (Θ , e₁ <: e₂) ; Γᵐ ; Γᵒ ⊢ M ↝ M′ ⦂ A
      ---------------------------------------------------------------------------
    → Δ ; Θ ; Γᵐ ; Γᵒ ⊢ (e₁ <: e₂ => M) ↝ (e₁ <: e₂ => M′) ⦂ e₁ <: e₂ => A

  meta-subelim : ∀ {A e₁ e₂ M M′ ℓ}
    → Θ ⊢ᵉ e₁ <: e₂
    → Δ ; Θ ; Γᵐ ; Γᵒ ⊢ M ↝ M′ ⦂ e₁ <: e₂ => A
      ---------------------------------------------
    → Δ ; Θ ; Γᵐ ; Γᵒ ⊢ M ●^ ℓ ↝ M′ ● ⦂ A

  meta-subelim⋆ : ∀ {M M′ ℓ}
    → Δ ; Θ ; Γᵐ ; Γᵒ ⊢ M ↝ M′ ⦂ ⋆
      ---------------------------------------------
    → Δ ; Θ ; Γᵐ ; Γᵒ ⊢ M ●^ ℓ ↝ M′ ★ ℓ ⦂ ⋆

  meta-quote : ∀ {T O e M M′}
    → Δ ⊢ᵉ e
    → Δ ; Θ ; Γᵐ ; Γᵒ ; e ⊢ M ↝ M′ ⭆ T
    → O ↪ᵒ T
      ---------------------------------------------------------
    → Δ ; Θ ; Γᵐ ; Γᵒ ⊢ ‶ M ″ e ↝ ‶ M′ ″ e ⦂ ‶ O ″ ec e

  meta-ref : ∀ {A M M′}
    → Δ ; Θ ; Γᵐ ; Γᵒ ⊢ M ↝ M′ ⦂ A
      ------------------------------------------------
    → Δ ; Θ ; Γᵐ ; Γᵒ ⊢ ref M ↝ ref M′ ⦂ Ref A

  meta-assign : ∀ {A B L M L′ M′ ℓ}
    → Δ ; Θ ; Γᵐ ; Γᵒ ⊢ L ↝ L′ ⦂ Ref A
    → Δ ; Θ ; Γᵐ ; Γᵒ ⊢ M ↝ M′ ⦂ B
    → (B≲A : Θ ⊢ B ≲ A)
      ---------------------------------------------------------------------------
    → Δ ; Θ ; Γᵐ ; Γᵒ ⊢ L := M ^ ℓ ↝ L′ := (M′ ⟨ coerceᵐ B≲A ℓ ⟩) ⦂ ` Unit

  meta-assign⋆ : ∀ {A L M L′ M′ ℓ}
    → Δ ; Θ ; Γᵐ ; Γᵒ ⊢ L ↝ L′ ⦂ ⋆
    → Δ ; Θ ; Γᵐ ; Γᵒ ⊢ M ↝ M′ ⦂ A
      ---------------------------------------------------------------------------------
    → let ⋆⇒Ref⋆ = coerceᵐ (csub-⋆-left {Θ} {Ref ⋆}) ℓ in
       let    A⇒⋆ = coerceᵐ (csub-⋆-right {Θ} {A}) ℓ in
       Δ ; Θ ; Γᵐ ; Γᵒ ⊢ (L := M ^ ℓ) ↝ (L′ ⟨ ⋆⇒Ref⋆ ⟩) := (M′ ⟨ A⇒⋆ ⟩) ⦂ ` Unit

  meta-deref : ∀ {A M M′ ℓ}
    → Δ ; Θ ; Γᵐ ; Γᵒ ⊢ M ↝ M′ ⦂ Ref A
      ------------------------------------------
    → Δ ; Θ ; Γᵐ ; Γᵒ ⊢ ! M ^ ℓ ↝ ! M′ ⦂ A

  meta-deref⋆ : ∀ {M M′ ℓ}
    → Δ ; Θ ; Γᵐ ; Γᵒ ⊢ M ↝ M′ ⦂ ⋆
      ---------------------------------------------------------
    → let ⋆⇒Ref⋆ = coerceᵐ (csub-⋆-left {Θ} {Ref ⋆}) ℓ in
       Δ ; Θ ; Γᵐ ; Γᵒ ⊢ ! M ^ ℓ ↝ ! (M′ ⟨ ⋆⇒Ref⋆ ⟩) ⦂ ⋆
