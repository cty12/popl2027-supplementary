module Theories.SurfaceSyntaxAndTypeSystem where

open import Data.Nat using (zero)
open import Data.Product using () renaming (_,_ to ⟨_,_⟩)
open import Theories.Utils using (_∋_; _∋_⦂_)

open import Theories.EnvClassifiers  public hiding (size)
open import Theories.BaseTypes       public
open import Theories.MetaTypes       public
open import Theories.CodeTypes       public
open import Theories.BlameLabels     public
open import Theories.ConsistentSubtyping public
open import Theories.CCAlphaRefStarSyntaxAndTypeSystem
  using (Var)

infixl 7 _·_^_
infixl 7 _·[_]^_
infix 8 ~_^_
infix 8 _●^_
infixr 6 _:=_^_
infix 8 !_^_


data CodeSurfaceTerm : Set
data MetaSurfaceTerm : Set

data CodeSurfaceTerm where

  $_ : ∀ {ι} → base-rep ι → CodeSurfaceTerm

  `_ : Var → CodeSurfaceTerm

  ƛ_˙_ : OType → CodeSurfaceTerm → CodeSurfaceTerm

  _·_^_ : CodeSurfaceTerm → CodeSurfaceTerm → BlameLabel → CodeSurfaceTerm

  ~_^_ : MetaSurfaceTerm → BlameLabel → CodeSurfaceTerm


data MetaSurfaceTerm where

  $_ : ∀ {ι} → base-rep ι → MetaSurfaceTerm

  `_ : Var → MetaSurfaceTerm

  ƛ_˙_  : MType → MetaSurfaceTerm → MetaSurfaceTerm

  _·_^_ : MetaSurfaceTerm → MetaSurfaceTerm → BlameLabel → MetaSurfaceTerm

  Λ_ : MetaSurfaceTerm → MetaSurfaceTerm

  _·[_]^_ : MetaSurfaceTerm → EC → BlameLabel → MetaSurfaceTerm

  _<:_=>_  : EC → EC → MetaSurfaceTerm → MetaSurfaceTerm

  _●^_ : MetaSurfaceTerm → BlameLabel → MetaSurfaceTerm

  ‶_″_ : CodeSurfaceTerm → EC → MetaSurfaceTerm

  ref : MetaSurfaceTerm → MetaSurfaceTerm

  _:=_^_ : MetaSurfaceTerm → MetaSurfaceTerm → BlameLabel → MetaSurfaceTerm

  !_^_ : MetaSurfaceTerm → BlameLabel → MetaSurfaceTerm


⌈_⌉ᵒ : OType → OType⋆
⌈ ` ι ⌉ᵒ = ` ι
⌈ T₁ ⇒ T₂ ⌉ᵒ = ⌈ T₁ ⌉ᵒ ⇒ ⌈ T₂ ⌉ᵒ


⌈_⌉ᵒ-↪ : (T : OType) → ⌈ T ⌉ᵒ ↪ᵒ T
⌈ ` ι ⌉ᵒ-↪ = ` ι
⌈ T₁ ⇒ T₂ ⌉ᵒ-↪ = ⌈ T₁ ⌉ᵒ-↪ ⇒ ⌈ T₂ ⌉ᵒ-↪


infix 3 _;_;_;_;_⊢_⭆_
infix 3 _;_;_;_;_⊢_⭅_
infix 3 _;_;_;_⊢_⦂_


data _;_;_;_;_⊢_⭆_
  (Δ : ECCtx) (Θ : SubCtx) (Γᵐ : MCtx) (Γᵒ : OCtx) (e : EC)
  : CodeSurfaceTerm → OType → Set

data _;_;_;_;_⊢_⭅_
  (Δ : ECCtx) (Θ : SubCtx) (Γᵐ : MCtx) (Γᵒ : OCtx) (e : EC)
  : CodeSurfaceTerm → OType → Set

data _;_;_;_⊢_⦂_
  (Δ : ECCtx) (Θ : SubCtx) (Γᵐ : MCtx) (Γᵒ : OCtx)
  : MetaSurfaceTerm → MType → Set


data _;_;_;_;_⊢_⭆_ Δ Θ Γᵐ Γᵒ e where

  code-constˢ : ∀ {ι} {k : base-rep ι}
    → Δ ; Θ ; Γᵐ ; Γᵒ ; e ⊢ $ k ⭆ ` ι

  code-varˢ : ∀ {x T α}
    → Γᵒ ∋ᵒ x ⦂ ⟨ T , α ⟩
    → Θ ⊢ᵉ ` α <: e
      -----------------------------
    → Δ ; Θ ; Γᵐ ; Γᵒ ; e ⊢ ` x ⭆ T

  code-absˢ : ∀ {T₁ T₂ N}
    → Δ ,α ; (⇑ᵉ-subctx Θ , ⇑ᵉ-ec e <: ` zero) ; ⇑ᵉ-mctx Γᵐ ; (⇑ᵉ-octx Γᵒ , T₁ ＠ zero) ; ` zero
        ⊢ N ⭆ T₂
      --------------------------------------------------
    → Δ ; Θ ; Γᵐ ; Γᵒ ; e ⊢ ƛ T₁ ˙ N ⭆ T₁ ⇒ T₂

  code-appˢ : ∀ {T₁ T₂ L M ℓ}
    → Δ ; Θ ; Γᵐ ; Γᵒ ; e ⊢ L ⭆ T₁ ⇒ T₂
    → Δ ; Θ ; Γᵐ ; Γᵒ ; e ⊢ M ⭅ T₁
      ------------------------------------------
    → Δ ; Θ ; Γᵐ ; Γᵒ ; e ⊢ L · M ^ ℓ ⭆ T₂


data _;_;_;_;_⊢_⭅_ Δ Θ Γᵐ Γᵒ e where

  spliceˢ : ∀ {T A M ℓ}
    → Δ ; Θ ; Γᵐ ; Γᵒ ⊢ M ⦂ A
    → (A≲T : Θ ⊢ A ≲ ‶ ⌈ T ⌉ᵒ ″ ec e)
      ------------------------------------------
    → Δ ; Θ ; Γᵐ ; Γᵒ ; e ⊢ ~ M ^ ℓ ⭅ T

  checkˢ : ∀ {T M}
    → Δ ; Θ ; Γᵐ ; Γᵒ ; e ⊢ M ⭆ T
      -----------------------------
    → Δ ; Θ ; Γᵐ ; Γᵒ ; e ⊢ M ⭅ T


data _;_;_;_⊢_⦂_ Δ Θ Γᵐ Γᵒ where

  meta-constˢ : ∀ {ι} {k : base-rep ι}
    → Δ ; Θ ; Γᵐ ; Γᵒ ⊢ $ k ⦂ ` ι

  meta-varˢ : ∀ {x A}
    → Γᵐ ∋ x ⦂ A
      -----------------------
    → Δ ; Θ ; Γᵐ ; Γᵒ ⊢ ` x ⦂ A

  meta-absˢ : ∀ {A B M}
    → Δ ⊢ᵐᵗ A
    → Δ ; Θ ; (Γᵐ ⸴ A) ; Γᵒ ⊢ M ⦂ B
      ------------------------------------------
    → Δ ; Θ ; Γᵐ ; Γᵒ ⊢ ƛ A ˙ M ⦂ A ⇒ B

  meta-appˢ : ∀ {A₁ A₂ B L M ℓ}
    → Δ ; Θ ; Γᵐ ; Γᵒ ⊢ L ⦂ A₁ ⇒ A₂
    → Δ ; Θ ; Γᵐ ; Γᵒ ⊢ M ⦂ B
    → (B≲A₁ : Θ ⊢ B ≲ A₁)
      --------------------------------------------
    → Δ ; Θ ; Γᵐ ; Γᵒ ⊢ L · M ^ ℓ ⦂ A₂

  meta-app⋆ˢ : ∀ {A L M ℓ}
    → Δ ; Θ ; Γᵐ ; Γᵒ ⊢ L ⦂ ⋆
    → Δ ; Θ ; Γᵐ ; Γᵒ ⊢ M ⦂ A
      ---------------------------------
    → Δ ; Θ ; Γᵐ ; Γᵒ ⊢ L · M ^ ℓ ⦂ ⋆

  meta-ecabsˢ : ∀ {A M}
    → Δ ,α ; ⇑ᵉ-subctx Θ ; ⇑ᵉ-mctx Γᵐ ; ⇑ᵉ-octx Γᵒ ⊢ M ⦂ A
      --------------------------------------------------------
    → Δ ; Θ ; Γᵐ ; Γᵒ ⊢ Λ M ⦂ ∀̇ A

  meta-ecappˢ : ∀ {A M e ℓ}
    → Δ ⊢ᵉ e
    → Δ ; Θ ; Γᵐ ; Γᵒ ⊢ M ⦂ ∀̇ A
      --------------------------------------------
    → Δ ; Θ ; Γᵐ ; Γᵒ ⊢ M ·[ e ]^ ℓ ⦂ A [ e ]ᵉ

  meta-ecapp⋆ˢ : ∀ {M e ℓ}
    → Δ ⊢ᵉ e
    → Δ ; Θ ; Γᵐ ; Γᵒ ⊢ M ⦂ ⋆
      ---------------------------------
    → Δ ; Θ ; Γᵐ ; Γᵒ ⊢ M ·[ e ]^ ℓ ⦂ ⋆

  meta-subintroˢ : ∀ {A e₁ e₂ M}
    → Δ ⊢ᵉ e₁
    → Δ ⊢ᵉ e₂
    → Δ ; (Θ , e₁ <: e₂) ; Γᵐ ; Γᵒ ⊢ M ⦂ A
      ---------------------------------------------------------
    → Δ ; Θ ; Γᵐ ; Γᵒ ⊢ e₁ <: e₂ => M ⦂ e₁ <: e₂ => A

  meta-subelimˢ : ∀ {A e₁ e₂ M ℓ}
    → Θ ⊢ᵉ e₁ <: e₂
    → Δ ; Θ ; Γᵐ ; Γᵒ ⊢ M ⦂ e₁ <: e₂ => A
      --------------------------------------------
    → Δ ; Θ ; Γᵐ ; Γᵒ ⊢ M ●^ ℓ ⦂ A

  meta-subelim⋆ˢ : ∀ {M ℓ}
    → Δ ; Θ ; Γᵐ ; Γᵒ ⊢ M ⦂ ⋆
      -----------------------------
    → Δ ; Θ ; Γᵐ ; Γᵒ ⊢ M ●^ ℓ ⦂ ⋆

  meta-quoteˢ : ∀ {T e M}
    → Δ ⊢ᵉ e
    → Δ ; Θ ; Γᵐ ; Γᵒ ; e ⊢ M ⭆ T
      ----------------------------------------------------
    → Δ ; Θ ; Γᵐ ; Γᵒ ⊢ ‶ M ″ e ⦂ ‶ ⌈ T ⌉ᵒ ″ ec e

  meta-refˢ : ∀ {A M}
    → Δ ; Θ ; Γᵐ ; Γᵒ ⊢ M ⦂ A
      ---------------------------------
    → Δ ; Θ ; Γᵐ ; Γᵒ ⊢ ref M ⦂ Ref A

  meta-assignˢ : ∀ {A B L M ℓ}
    → Δ ; Θ ; Γᵐ ; Γᵒ ⊢ L ⦂ Ref A
    → Δ ; Θ ; Γᵐ ; Γᵒ ⊢ M ⦂ B
    → (B≲A : Θ ⊢ B ≲ A)
      ---------------------------------------------
    → Δ ; Θ ; Γᵐ ; Γᵒ ⊢ L := M ^ ℓ ⦂ ` Unit

  meta-assign⋆ˢ : ∀ {A L M ℓ}
    → Δ ; Θ ; Γᵐ ; Γᵒ ⊢ L ⦂ ⋆
    → Δ ; Θ ; Γᵐ ; Γᵒ ⊢ M ⦂ A
      ----------------------------------
    → Δ ; Θ ; Γᵐ ; Γᵒ ⊢ L := M ^ ℓ ⦂ ` Unit

  meta-derefˢ : ∀ {A M ℓ}
    → Δ ; Θ ; Γᵐ ; Γᵒ ⊢ M ⦂ Ref A
      -----------------------------
    → Δ ; Θ ; Γᵐ ; Γᵒ ⊢ ! M ^ ℓ ⦂ A

  meta-deref⋆ˢ : ∀ {M ℓ}
    → Δ ; Θ ; Γᵐ ; Γᵒ ⊢ M ⦂ ⋆
      -----------------------------
    → Δ ; Θ ; Γᵐ ; Γᵒ ⊢ ! M ^ ℓ ⦂ ⋆
