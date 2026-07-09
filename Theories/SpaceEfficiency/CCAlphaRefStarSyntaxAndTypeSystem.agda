{-

  Syntax and type system for the cast calculus of λαRef⋆ with
  space-efficient hypercoercions.

-}

module Theories.SpaceEfficiency.CCAlphaRefStarSyntaxAndTypeSystem where

open import Data.Nat using (zero)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Theories.Utils using (_∋_; _∋_⦂_; ∅; ⟨_,_,_,_⟩)
open import Theories.EnvClassifiers public
open import Theories.BaseTypes      public
open import Theories.MetaTypes      public
open import Theories.CodeTypes      public
open import Theories.BlameLabels    public
open import Theories.CCAlphaRefStarSyntaxAndTypeSystem
  using (Var; Addr; HeapCtx; ⇑ᵉ-heapctx; ⇑ᵉ-heapctx-snoc; Ctx; ⇑ᵉ-ctx;
         _⊢_HeapCtx; _⊢_Ctx; wf-ctx)
  public
import Theories.SpaceEfficiency.MetaHypercoercions as MH
open MH using (MHypercoercion) public


-- +-----------------+ --
-- | Raw term syntax | --
-- +-----------------+ --

infix 8 `_
infix 8 addr_
infix 8 ~_
infix 8 !_
infix 8 _●
infix 8 _★_
infix 8 _⟨_⟩
infix 8 ‶_″_
infix 8 ƛ_˙_
infix 8 ƛ̅_˙_
infixl 7 _·_
infixl 7 _·[_]
infixr 6 _:=_

data CodeTerm : Set
data MetaTerm : Set

data CodeTerm where
  $_       : ∀ {ι} → base-rep ι → CodeTerm
  `_       : Var → CodeTerm
  ƛ_˙_     : OType → CodeTerm → CodeTerm
  ƛ̅_˙_     : EC → CodeTerm → CodeTerm
  _·_      : CodeTerm → CodeTerm → CodeTerm
  ~_       : MetaTerm → CodeTerm
  blameᵒ   : BlameLabel → CodeTerm

data MetaTerm where
  $_       : ∀ {ι} → base-rep ι → MetaTerm
  `_       : Var → MetaTerm
  addr_    : Addr → MetaTerm
  ƛ_       : MetaTerm → MetaTerm
  _·_      : MetaTerm → MetaTerm → MetaTerm
  Λ_       : MetaTerm → MetaTerm
  _·[_]    : MetaTerm → EC → MetaTerm
  _<:_=>_  : EC → EC → MetaTerm → MetaTerm
  _●       : MetaTerm → MetaTerm
  _★_      : MetaTerm → BlameLabel → MetaTerm
  ‶_″_     : CodeTerm → EC → MetaTerm
  ref      : MetaTerm → MetaTerm
  _:=_     : MetaTerm → MetaTerm → MetaTerm
  !_       : MetaTerm → MetaTerm
  _⟨_⟩     : MetaTerm → MHypercoercion → MetaTerm
  blame    : BlameLabel → MetaTerm


-- +------------+ --
-- | Type rules | --
-- +------------+ --

infix 3 _;_;_⊢ᵒ_⦂_
infix 3 _;_⊢ᵐ_⦂_

-- | Δ ; Γ ; e ⊢ Mᵒ : T
data _;_;_⊢ᵒ_⦂_ : ECCtx → Ctx → EC → CodeTerm → OType → Set

-- | Δ ; Γ ⊢ M : A
data _;_⊢ᵐ_⦂_ : ECCtx → Ctx → MetaTerm → MType → Set

data _;_;_⊢ᵒ_⦂_ where

  ⊢constᵒ : ∀ {Δ Γ e ι}
    → (r : base-rep ι)
      ---------------------------
    → Δ ; Γ ; e ⊢ᵒ $ r ⦂ ` ι

  ⊢varᵒ : ∀ {Δ Θ Γᵒ Γᵐ Σ x T e α}
    → Γᵒ ∋ᵒ x ⦂ ⟨ T , α ⟩
    → Θ ⊢ᵉ ` α <: e
      ---------------------------------------------
    → Δ ; ⟨ Θ , Γᵒ , Γᵐ , Σ ⟩ ; e ⊢ᵒ ` x ⦂ T

  ⊢lamᵒ : ∀ {Δ Θ Γᵒ Γᵐ Σ T₁ T₂ e M}
    → let Θ′  = ⇑ᵉ-subctx Θ , ⇑ᵉ-ec e <: ` zero in
       let Γᵒ′ = ⇑ᵉ-octx Γᵒ , T₁ ＠ zero in
       let Γᵐ′ = ⇑ᵉ-mctx Γᵐ in
       let Σ′  = ⇑ᵉ-heapctx Σ in
       Δ ,α ; ⟨ Θ′ , Γᵒ′ , Γᵐ′ , Σ′ ⟩ ; ` zero ⊢ᵒ M ⦂ T₂
      ------------------------------------------------------------
    → Δ ; ⟨ Θ , Γᵒ , Γᵐ , Σ ⟩ ; e ⊢ᵒ ƛ T₁ ˙ M ⦂ T₁ ⇒ T₂

  ⊢lamᵒ-val : ∀ {Δ Θ Γᵒ Γᵐ Σ T₁ T₂ e₁ e₂ M α}
    → GlobalEC Δ α
    → GlobalEntries Γᵒ ∋ ⟨ T₁ , α ⟩
    → GlobalEdges   Θ  ∋ ⟨ e₁ , ` α ⟩
    → Θ ⊢ᵉ e₁ <: e₂
    → Δ ; ⟨ Θ , Γᵒ , Γᵐ , Σ ⟩ ; ` α ⊢ᵒ M ⦂ T₂
      ------------------------------------------------------------
    → Δ ; ⟨ Θ , Γᵒ , Γᵐ , Σ ⟩ ; e₂ ⊢ᵒ ƛ̅ ` α ˙ M ⦂ T₁ ⇒ T₂

  ⊢appᵒ : ∀ {Δ Γ T₁ T₂ e L M}
    → Δ ; Γ ; e ⊢ᵒ L ⦂ T₁ ⇒ T₂
    → Δ ; Γ ; e ⊢ᵒ M ⦂ T₁
      ---------------------------------------
    → Δ ; Γ ; e ⊢ᵒ L · M ⦂ T₂

  ⊢splice : ∀ {Δ Γ O T e M}
    → Δ ; Γ ⊢ᵐ M ⦂ ‶ O ″ ec e
    → O ↪ᵒ T
      ---------------------------------------
    → Δ ; Γ ; e ⊢ᵒ ~ M ⦂ T

  ⊢blameᵒ : ∀ {Δ Γ e T}
    → (ℓ : BlameLabel)
      ---------------------------
    → Δ ; Γ ; e ⊢ᵒ blameᵒ ℓ ⦂ T


data _;_⊢ᵐ_⦂_ where

  ⊢constᵐ : ∀ {Δ Γ ι}
    → (r : base-rep ι)
      ------------------------
    → Δ ; Γ ⊢ᵐ $ r ⦂ ` ι

  ⊢varᵐ : ∀ {Δ Θ Γᵒ Γᵐ Σ x A}
    → Γᵐ ∋ x ⦂ A
      ------------------------------------------
    → Δ ; ⟨ Θ , Γᵒ , Γᵐ , Σ ⟩ ⊢ᵐ ` x ⦂ A

  ⊢addr : ∀ {Δ Θ Γᵒ Γᵐ Σ A a}
    → Σ ∋ a ⦂ A
      ------------------------------------------------
    → Δ ; ⟨ Θ , Γᵒ , Γᵐ , Σ ⟩ ⊢ᵐ addr a ⦂ Ref A

  ⊢lamᵐ : ∀ {Δ Θ Γᵒ Γᵐ Σ A B M}
    → Δ ⊢ᵐᵗ A
    → Δ ; ⟨ Θ , Γᵒ , Γᵐ ⸴ A , Σ ⟩ ⊢ᵐ M ⦂ B
      ------------------------------------------------
    → Δ ; ⟨ Θ , Γᵒ , Γᵐ , Σ ⟩ ⊢ᵐ ƛ M ⦂ (A ⇒ B)

  ⊢appᵐ : ∀ {Δ Γ A B L M}
    → Δ ; Γ ⊢ᵐ L ⦂ (A ⇒ B)
    → Δ ; Γ ⊢ᵐ M ⦂ A
      ---------------------------
    → Δ ; Γ ⊢ᵐ L · M ⦂ B

  ⊢eclam : ∀ {Δ Γ A M}
    → Δ ,α ; ⇑ᵉ-ctx Γ ⊢ᵐ M ⦂ A
      ------------------------------
    → Δ ; Γ ⊢ᵐ Λ M ⦂ ∀̇ A

  ⊢ecapp : ∀ {Δ Γ A M e}
    → Δ ; Γ ⊢ᵐ M ⦂ ∀̇ A
    → Δ ⊢ᵉ e
      ---------------------------------
    → Δ ; Γ ⊢ᵐ M ·[ e ] ⦂ A [ e ]ᵉ

  ⊢subintro : ∀ {Δ Θ Γᵒ Γᵐ Σ A M e₁ e₂}
    → Δ ⊢ᵉ e₁
    → Δ ⊢ᵉ e₂
    → Δ ; ⟨ Θ , e₁ <: e₂ , Γᵒ , Γᵐ , Σ ⟩ ⊢ᵐ M ⦂ A
      ---------------------------------------------------------------
    → Δ ; ⟨ Θ , Γᵒ , Γᵐ , Σ ⟩ ⊢ᵐ e₁ <: e₂ => M ⦂ e₁ <: e₂ => A

  ⊢subelim : ∀ {Δ Θ Γᵒ Γᵐ Σ A e₁ e₂ M}
    → Δ ; ⟨ Θ , Γᵒ , Γᵐ , Σ ⟩ ⊢ᵐ M ⦂ e₁ <: e₂ => A
    → Θ ⊢ᵉ e₁ <: e₂
      ------------------------------------------------
    → Δ ; ⟨ Θ , Γᵒ , Γᵐ , Σ ⟩ ⊢ᵐ M ● ⦂ A

  ⊢subelim⋆ : ∀ {Δ Γ M}
    → Δ ; Γ ⊢ᵐ M ⦂ ⋆
    → (ℓ : BlameLabel)
      ---------------------------
    → Δ ; Γ ⊢ᵐ M ★ ℓ ⦂ ⋆

  ⊢quote : ∀ {Δ Γ T O M e}
    → Δ ; Γ ; e ⊢ᵒ M ⦂ T
    → Δ ⊢ᵉ e
    → O ↪ᵒ T
      ------------------------------------
    → Δ ; Γ ⊢ᵐ ‶ M ″ e ⦂ ‶ O ″ ec e

  ⊢ref : ∀ {Δ Γ A M}
    → Δ ; Γ ⊢ᵐ M ⦂ A
      ----------------------------
    → Δ ; Γ ⊢ᵐ ref M ⦂ Ref A

  ⊢assign : ∀ {Δ Γ A M N}
    → Δ ; Γ ⊢ᵐ M ⦂ Ref A
    → Δ ; Γ ⊢ᵐ N ⦂ A
      ----------------------------
    → Δ ; Γ ⊢ᵐ M := N ⦂ ` Unit

  ⊢deref : ∀ {Δ Γ A M}
    → Δ ; Γ ⊢ᵐ M ⦂ Ref A
      ----------------------------
    → Δ ; Γ ⊢ᵐ ! M ⦂ A

  ⊢cast : ∀ {Δ Θ Γᵒ Γᵐ Σ A B M c}
    → Δ ; ⟨ Θ , Γᵒ , Γᵐ , Σ ⟩ ⊢ᵐ M ⦂ A
    → MH._;_⊢ᵐ_⦂_⇒_ Δ Θ c A B
      ---------------------------------------------
    → Δ ; ⟨ Θ , Γᵒ , Γᵐ , Σ ⟩ ⊢ᵐ M ⟨ c ⟩ ⦂ B

  ⊢blame : ∀ {Δ Γ A}
    → Δ ⊢ᵐᵗ A
    → (ℓ : BlameLabel)
      ----------------------------
    → Δ ; Γ ⊢ᵐ blame ℓ ⦂ A
