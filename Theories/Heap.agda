module Theories.Heap where

open import Data.List using (List; []; _∷_; _∷ʳ_; length)
open import Data.Nat using (ℕ; zero; suc)

open import Theories.Utils using (_∋_⦂_; ∅; ⟨_,_,_,_⟩)
import Theories.Utils as U
open import Theories.CCAlphaRefStarSyntaxAndTypeSystem
open import Theories.CodeCtxWeakening
  using (meta-octx-weaken)
open import Theories.ECCtxWeakening
  using (_⊆ᵉ_; ⊆ᵉ-snoc; meta-ecctx-weaken)
open import Theories.HeapCtxWeakening
open import Theories.SubCtxWeakening
  using (subctx-lex-weaken; subctx-global-weaken; meta-⊆ˢ)


-- +------------------------------+ --
-- | Runtime heap operations      | --
-- +------------------------------+ --

Heap : Set
Heap = List MetaTerm

infix 4 _⟦_↦_⟧=_

data _⟦_↦_⟧=_ {A : Set} : List A → ℕ → A → List A → Set where

  here : ∀ {xs x y}
      ------------------------------------
    → (x ∷ xs) ⟦ zero ↦ y ⟧= y ∷ xs

  there : ∀ {xs xs′ x y n}
    → xs ⟦ n ↦ y ⟧= xs′
      ------------------------------------------
    → (x ∷ xs) ⟦ suc n ↦ y ⟧= x ∷ xs′


-- | Runtime heap typing.  The last Σ parameter is the full heap context
-- | under which every stored term is checked; the middle heap-context
-- | argument tracks the pointwise shape of the remaining heap entries.
data HeapTyping (Δ : ECCtx) (Θ : SubCtx) (Γᵒ : OCtx) (Σ : HeapCtx) :
  Heap → HeapCtx → Set where

  ht-∅ : HeapTyping Δ Θ Γᵒ Σ [] []

  ht-, : ∀ {μ Σ′ V A}
    → Δ ; ⟨ Θ , Γᵒ , ∅ , Σ ⟩ ⊢ᵐ V ⦂ A
    → HeapTyping Δ Θ Γᵒ Σ μ Σ′
      -------------------------------------
    → HeapTyping Δ Θ Γᵒ Σ (V ∷ μ) (A ∷ Σ′)

infix 4 _;_;_;_⊢ᴴ_

_;_;_;_⊢ᴴ_ : ECCtx → SubCtx → OCtx → HeapCtx → Heap → Set
Δ ; Θ ; Γᵒ ; Σ ⊢ᴴ μ = HeapTyping Δ Θ Γᵒ Σ μ Σ


------------------------------------------------------------------------
-- Heap typing lemmas

heap-ecctx-weaken : ∀ {Δ₁ Δ₂ Θ Γᵒ Σ μ Σ′}
  → Δ₁ ⊆ᵉ Δ₂
  → HeapTyping Δ₁ Θ Γᵒ Σ μ Σ′
    --------------------------------
  → HeapTyping Δ₂ Θ Γᵒ Σ μ Σ′
heap-ecctx-weaken Δ₁⊆Δ₂ ht-∅ = ht-∅
heap-ecctx-weaken Δ₁⊆Δ₂ (ht-, ⊢V ⊢μ) =
  ht-, (meta-ecctx-weaken Δ₁⊆Δ₂ ⊢V) (heap-ecctx-weaken Δ₁⊆Δ₂ ⊢μ)

heap-ecctx-snoc : ∀ {Δ Θ Γᵒ Σ μ Σ′}
  → HeapTyping Δ Θ Γᵒ Σ μ Σ′
    --------------------------------
  → HeapTyping (Δ ,ᵍα) Θ Γᵒ Σ μ Σ′
heap-ecctx-snoc {Δ = Δ} = heap-ecctx-weaken (⊆ᵉ-snoc {Δ = Δ})

heap-subctx-⊆ : ∀ {Δ Θ₁ Θ₂ Γᵒ Σ μ Σ′}
  → Θ₁ ⊆ˢ Θ₂
  → HeapTyping Δ Θ₁ Γᵒ Σ μ Σ′
    -----------------------------------
  → HeapTyping Δ Θ₂ Γᵒ Σ μ Σ′
heap-subctx-⊆ Θ₁⊆Θ₂ ht-∅ = ht-∅
heap-subctx-⊆ Θ₁⊆Θ₂ (ht-, ⊢V ⊢μ) =
  ht-, (meta-⊆ˢ Θ₁⊆Θ₂ ⊢V) (heap-subctx-⊆ Θ₁⊆Θ₂ ⊢μ)

heap-subctx-weaken : ∀ {Δ Θ Γᵒ Σ μ Σ′ e₁ e₂}
  → HeapTyping Δ Θ Γᵒ Σ μ Σ′
    -----------------------------------------
  → HeapTyping Δ (Θ , e₁ <: e₂) Γᵒ Σ μ Σ′
heap-subctx-weaken = heap-subctx-⊆ subctx-lex-weaken

heap-octx-snoc : ∀ {Δ Θ Γᵒ Σ μ Σ′ T α}
  → HeapTyping Δ Θ Γᵒ Σ μ Σ′
    ----------------------------------------------
  → HeapTyping Δ Θ (Γᵒ ,ᵍ T ＠ α) Σ μ Σ′
heap-octx-snoc ht-∅ = ht-∅
heap-octx-snoc (ht-, ⊢V ⊢μ) =
  ht-, (meta-octx-weaken ⊢V) (heap-octx-snoc ⊢μ)

heap-code-alloc : ∀ {Δ Θ Γᵒ Σ μ e T}
  → Δ ; Θ ; Γᵒ ; Σ ⊢ᴴ μ
    ----------------------------------------------------------------
  → Δ ,ᵍα ; Θ ,ᵍ e <: ` freshᵉ Δ ; Γᵒ ,ᵍ T ＠ freshᵉ Δ ; Σ ⊢ᴴ μ
heap-code-alloc ⊢μ =
  heap-octx-snoc (heap-subctx-⊆ subctx-global-weaken (heap-ecctx-snoc ⊢μ))

heap-extend : ∀ {Δ Θ Γᵒ Σ μ Σ′ V A}
  → HeapTyping Δ Θ Γᵒ Σ μ Σ′
  → Δ ; ⟨ Θ , Γᵒ , ∅ , Σ ⟩ ⊢ᵐ V ⦂ A
    -------------------------------------------------
  → HeapTyping Δ Θ Γᵒ (Σ ∷ʳ A) (μ ∷ʳ V) (Σ′ ∷ʳ A)
heap-extend ht-∅ ⊢V = ht-, (meta-heapctx-weaken ⊢V) ht-∅
heap-extend (ht-, ⊢W ⊢μ) ⊢V =
  ht-, (meta-heapctx-weaken ⊢W) (heap-extend ⊢μ ⊢V)

heap-fresh-lookup : ∀ {Δ Θ Γᵒ Σ μ Σ′ A}
  → HeapTyping Δ Θ Γᵒ Σ μ Σ′
    -------------------------------
  → Σ′ ∷ʳ A ∋ length μ ⦂ A
heap-fresh-lookup ht-∅ = U.here
heap-fresh-lookup (ht-, ⊢V ⊢μ) = U.there (heap-fresh-lookup ⊢μ)

heap-lookup : ∀ {Δ Θ Γᵒ Σ μ Σ′ a V A}
  → HeapTyping Δ Θ Γᵒ Σ μ Σ′
  → μ ∋ a ⦂ V
  → Σ′ ∋ a ⦂ A
    -------------------------------------
  → Δ ; ⟨ Θ , Γᵒ , ∅ , Σ ⟩ ⊢ᵐ V ⦂ A
heap-lookup (ht-, ⊢V ⊢μ) U.here U.here = ⊢V
heap-lookup (ht-, ⊢W ⊢μ) (U.there μ∋V) (U.there Σ∋A) =
  heap-lookup ⊢μ μ∋V Σ∋A

heap-update : ∀ {Δ Θ Γᵒ Σ μ μ′ Σ′ a V A}
  → HeapTyping Δ Θ Γᵒ Σ μ Σ′
  → μ ⟦ a ↦ V ⟧= μ′
  → Σ′ ∋ a ⦂ A
  → Δ ; ⟨ Θ , Γᵒ , ∅ , Σ ⟩ ⊢ᵐ V ⦂ A
    -----------------------------------------
  → HeapTyping Δ Θ Γᵒ Σ μ′ Σ′
heap-update (ht-, ⊢W ⊢μ) here U.here ⊢V = ht-, ⊢V ⊢μ
heap-update (ht-, ⊢W ⊢μ) (there μ↦μ′) (U.there Σ∋A) ⊢V =
  ht-, ⊢W (heap-update ⊢μ μ↦μ′ Σ∋A ⊢V)
