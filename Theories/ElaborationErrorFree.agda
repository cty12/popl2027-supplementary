module Theories.ElaborationErrorFree where

open import Data.List.Relation.Unary.All using (All) renaming ([] to []ᴬ; _∷_ to _∷ᴬ_)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)

open import Theories.Utils using (_∋_⦂_; lookup-all; lookup->member)
open import Theories.EnvClassifiers
open import Theories.MetaTypes
open import Theories.CodeTypes
open import Theories.SurfaceFullyStatic
open import Theories.Elaboration
open import Theories.Coerce
open import Theories.ErrorFree


-- | For open terms, fully-static syntax is not enough: a variable from Γᵐ
-- may have type ⋆, and then elaboration can validly use a ⋆ rule that inserts
-- a projection.  The error-free theorem therefore assumes Γᵐ is static too.
FullyStaticMCtx : MCtx → Set
FullyStaticMCtx = All FullyStaticMType


fs-renᵉ-mtype : ∀ ρ {A}
  → FullyStaticMType A
    ---------------------------------
  → FullyStaticMType (renᵉ ρ A)
fs-renᵉ-mtype ρ static-baseᵐ = static-baseᵐ
fs-renᵉ-mtype ρ (static-funᵐ fsA fsB) =
  static-funᵐ (fs-renᵉ-mtype ρ fsA) (fs-renᵉ-mtype ρ fsB)
fs-renᵉ-mtype ρ (static-refᵐ fsA) =
  static-refᵐ (fs-renᵉ-mtype ρ fsA)
fs-renᵉ-mtype ρ (static-codeᵐ fsO static-ec) =
  static-codeᵐ fsO static-ec
fs-renᵉ-mtype ρ (static-forallᵐ fsA) =
  static-forallᵐ (fs-renᵉ-mtype (extᵉ ρ) fsA)
fs-renᵉ-mtype ρ (static-subᵐ fsA) =
  static-subᵐ (fs-renᵉ-mtype ρ fsA)


fs-subᵉ-mtype : ∀ σ {A}
  → FullyStaticMType A
    ---------------------------------
  → FullyStaticMType (subᵉ σ A)
fs-subᵉ-mtype σ static-baseᵐ = static-baseᵐ
fs-subᵉ-mtype σ (static-funᵐ fsA fsB) =
  static-funᵐ (fs-subᵉ-mtype σ fsA) (fs-subᵉ-mtype σ fsB)
fs-subᵉ-mtype σ (static-refᵐ fsA) =
  static-refᵐ (fs-subᵉ-mtype σ fsA)
fs-subᵉ-mtype σ (static-codeᵐ fsO static-ec) =
  static-codeᵐ fsO static-ec
fs-subᵉ-mtype σ (static-forallᵐ fsA) =
  static-forallᵐ (fs-subᵉ-mtype (extsᵉ σ) fsA)
fs-subᵉ-mtype σ (static-subᵐ fsA) =
  static-subᵐ (fs-subᵉ-mtype σ fsA)


fs-⇑ᵉ-mctx : ∀ {Γᵐ}
  → FullyStaticMCtx Γᵐ
    ---------------------------------
  → FullyStaticMCtx (⇑ᵉ-mctx Γᵐ)
fs-⇑ᵉ-mctx []ᴬ = []ᴬ
fs-⇑ᵉ-mctx (fsA ∷ᴬ fsΓᵐ) = fs-renᵉ-mtype suc fsA ∷ᴬ fs-⇑ᵉ-mctx fsΓᵐ


fs-lookup : ∀ {Γᵐ x A}
  → FullyStaticMCtx Γᵐ
  → Γᵐ ∋ x ⦂ A
    ----------------------
  → FullyStaticMType A
fs-lookup fsΓᵐ lookup = lookup-all fsΓᵐ (lookup->member lookup)


↪ᵒ-fully-static : ∀ {O T}
  → O ↪ᵒ T
    -------------------
  → FullyStaticOType⋆ O
↪ᵒ-fully-static (` ι) = static-baseᵒ
↪ᵒ-fully-static (O₁↪T₁ ⇒ O₂↪T₂) =
  static-funᵒ (↪ᵒ-fully-static O₁↪T₁) (↪ᵒ-fully-static O₂↪T₂)


coerceᵉ-error-free : ∀ {Θ ê₁ ê₂ ℓ}
  → FullyStaticEC⋆ ê₁
  → FullyStaticEC⋆ ê₂
  → (ê₁≲ê₂ : Θ ⊢ᵉ ê₁ ≲ ê₂)
    ------------------------------------------
  → ErrorFreeECCoercion (coerceᵉ ê₁≲ê₂ ℓ)
coerceᵉ-error-free () fs csubᵉ-⋆-left
coerceᵉ-error-free fs () csubᵉ-⋆-right
coerceᵉ-error-free static-ec static-ec (csubᵉ-ec sub) =
  ef-↑ᵉ ∷ᴬ []ᴬ


coerceᵒ-error-free : ∀ {O₁ O₂ ℓ}
  → FullyStaticOType⋆ O₁
  → FullyStaticOType⋆ O₂
  → (O₁≲O₂ : O₁ ≲ᵒ O₂)
    ---------------------------------------
  → ErrorFreeCodeCoercion (coerceᵒ O₁≲O₂ ℓ)
coerceᵒ-error-free () fs csubᵒ-⋆-left
coerceᵒ-error-free fs () csubᵒ-⋆-right
coerceᵒ-error-free static-baseᵒ static-baseᵒ csubᵒ-base =
  []ᴬ
coerceᵒ-error-free (static-funᵒ fsA fsB) (static-funᵒ fsA′ fsB′) (csubᵒ-fun A′≲A B≲B′) =
  ef-funᵒ (coerceᵒ-error-free fsA′ fsA A′≲A)
          (coerceᵒ-error-free fsB fsB′ B≲B′) ∷ᴬ []ᴬ


mutual

  coerceᵐ-error-free : ∀ {Θ A B ℓ}
    → FullyStaticMType A
    → FullyStaticMType B
    → (A≲B : Θ ⊢ A ≲ B)
      ---------------------------------------
    → ErrorFreeMetaCoercion (coerceᵐ A≲B ℓ)
  coerceᵐ-error-free () fsB csub-⋆-left
  coerceᵐ-error-free fsA () csub-⋆-right
  coerceᵐ-error-free static-baseᵐ static-baseᵐ csub-base =
    []ᴬ
  coerceᵐ-error-free (static-funᵐ fsA fsB) (static-funᵐ fsA′ fsB′) (csub-fun A′≲A B≲B′) =
    ef-funᵐ (coerceᵐ-error-free fsA′ fsA A′≲A)
            (coerceᵐ-error-free fsB fsB′ B≲B′) ∷ᴬ []ᴬ
  coerceᵐ-error-free (static-refᵐ fsA) (static-refᵐ fsB) (csub-ref A≲B B≲A) =
    ef-refᵐ (coerceᵐ-error-free fsB fsA B≲A)
            (coerceᵐ-error-free fsA fsB A≲B) ∷ᴬ []ᴬ
  coerceᵐ-error-free (static-codeᵐ fsO fsE) (static-codeᵐ fsO′ fsE′) (csub-code O≲O′ e≲e′) =
    ef-codeᵐ (coerceᵒ-error-free fsO fsO′ O≲O′)
             (coerceᵉ-error-free fsE fsE′ e≲e′) ∷ᴬ []ᴬ
  coerceᵐ-error-free (static-forallᵐ fsA) (static-forallᵐ fsB) (csub-univ A≲B) =
    ef-forallᵐ (coerceᵐ-error-free fsA fsB A≲B) ∷ᴬ []ᴬ
  coerceᵐ-error-free (static-subᵐ fsA) (static-subᵐ fsB) (csub-sub A≲B) =
    ef-subᵐ (coerceᵐ-error-free fsA fsB A≲B) ∷ᴬ []ᴬ


mutual

  code-synth-error-free : ∀ {Δ Θ Γᵐ Γᵒ e M M′ T}
    → FullyStaticCodeSurfaceTerm M
    → FullyStaticMCtx Γᵐ
    → Δ ; Θ ; Γᵐ ; Γᵒ ; e ⊢ M ↝ M′ ⭆ T
      ---------------------------------------
    → ErrorFreeCodeTerm M′
  code-synth-error-free static-code-const fsΓᵐ code-const = ef-constᵒ
  code-synth-error-free static-code-var fsΓᵐ (code-var lookup sub) = ef-varᵒ
  code-synth-error-free (static-code-abs fsN) fsΓᵐ (code-abs elabN) =
    ef-lamᵒ (code-synth-error-free fsN (fs-⇑ᵉ-mctx fsΓᵐ) elabN)
  code-synth-error-free (static-code-app fsL fsM) fsΓᵐ (code-app elabL elabM) =
    ef-appᵒ (code-synth-error-free fsL fsΓᵐ elabL)
            (code-check-error-free fsM fsΓᵐ elabM)

  code-check-error-free : ∀ {Δ Θ Γᵐ Γᵒ e M M′ T}
    → FullyStaticCodeSurfaceTerm M
    → FullyStaticMCtx Γᵐ
    → Δ ; Θ ; Γᵐ ; Γᵒ ; e ⊢ M ↝ M′ ⭅ T
      ---------------------------------------
    → ErrorFreeCodeTerm M′
  code-check-error-free (static-splice fsM) fsΓᵐ (splice elabM A≲T O↪T)
    with meta-elab-error-free fsM fsΓᵐ elabM
  ... | ⟨ fsA , npM ⟩ =
    ef-splice
      (ef-cast npM
        (coerceᵐ-error-free fsA (static-codeᵐ (↪ᵒ-fully-static O↪T) static-ec) A≲T))
  code-check-error-free fsM fsΓᵐ (check elabM) =
    code-synth-error-free fsM fsΓᵐ elabM

  meta-elab-error-free : ∀ {Δ Θ Γᵐ Γᵒ M M′ A}
    → FullyStaticMetaSurfaceTerm M
    → FullyStaticMCtx Γᵐ
    → Δ ; Θ ; Γᵐ ; Γᵒ ⊢ M ↝ M′ ⦂ A
      ------------------------------------------------
    → FullyStaticMType A × ErrorFreeMetaTerm M′
  meta-elab-error-free static-meta-const fsΓᵐ meta-const =
    ⟨ static-baseᵐ , ef-constᵐ ⟩
  meta-elab-error-free static-meta-var fsΓᵐ (meta-var lookup) =
    ⟨ fs-lookup fsΓᵐ lookup , ef-varᵐ ⟩
  meta-elab-error-free (static-meta-abs fsA fsM) fsΓᵐ (meta-abs ⊢A elabM)
    with meta-elab-error-free fsM (fsA ∷ᴬ fsΓᵐ) elabM
  ... | ⟨ fsB , npM ⟩ = ⟨ static-funᵐ fsA fsB , ef-lamᵐ npM ⟩
  meta-elab-error-free (static-meta-app fsL fsM) fsΓᵐ (meta-app elabL elabM B≲A₁)
    with meta-elab-error-free fsL fsΓᵐ elabL | meta-elab-error-free fsM fsΓᵐ elabM
  ... | ⟨ static-funᵐ fsA₁ fsA₂ , npL ⟩ | ⟨ fsB , npM ⟩ =
    ⟨ fsA₂ , ef-appᵐ npL (ef-cast npM (coerceᵐ-error-free fsB fsA₁ B≲A₁)) ⟩
  meta-elab-error-free (static-meta-app fsL fsM) fsΓᵐ (meta-app⋆ elabL elabM)
    with meta-elab-error-free fsL fsΓᵐ elabL
  ... | ⟨ () , _ ⟩
  meta-elab-error-free (static-ecabs fsM) fsΓᵐ (meta-ecabs elabM)
    with meta-elab-error-free fsM (fs-⇑ᵉ-mctx fsΓᵐ) elabM
  ... | ⟨ fsA , npM ⟩ = ⟨ static-forallᵐ fsA , ef-eclam npM ⟩
  meta-elab-error-free (static-ecapp fsM) fsΓᵐ (meta-ecapp ⊢e elabM)
    with meta-elab-error-free fsM fsΓᵐ elabM
  ... | ⟨ static-forallᵐ fsA , npM ⟩ =
    ⟨ fs-subᵉ-mtype (_ •ᵉₛ idsᵉ) fsA , ef-ecapp npM ⟩
  meta-elab-error-free (static-ecapp fsM) fsΓᵐ (meta-ecapp⋆ ⊢e elabM)
    with meta-elab-error-free fsM fsΓᵐ elabM
  ... | ⟨ () , _ ⟩
  meta-elab-error-free (static-subintro fsM) fsΓᵐ (meta-subintro ⊢e₁ ⊢e₂ elabM)
    with meta-elab-error-free fsM fsΓᵐ elabM
  ... | ⟨ fsA , npM ⟩ = ⟨ static-subᵐ fsA , ef-subintro npM ⟩
  meta-elab-error-free (static-subelim fsM) fsΓᵐ (meta-subelim sub elabM)
    with meta-elab-error-free fsM fsΓᵐ elabM
  ... | ⟨ static-subᵐ fsA , npM ⟩ = ⟨ fsA , ef-subelim npM ⟩
  meta-elab-error-free (static-subelim fsM) fsΓᵐ (meta-subelim⋆ elabM)
    with meta-elab-error-free fsM fsΓᵐ elabM
  ... | ⟨ () , _ ⟩
  meta-elab-error-free (static-quote fsM) fsΓᵐ (meta-quote ⊢e elabM O↪T) =
    ⟨ static-codeᵐ (↪ᵒ-fully-static O↪T) static-ec
    , ef-quote (code-synth-error-free fsM fsΓᵐ elabM)
    ⟩
  meta-elab-error-free (static-ref fsM) fsΓᵐ (meta-ref elabM)
    with meta-elab-error-free fsM fsΓᵐ elabM
  ... | ⟨ fsA , npM ⟩ = ⟨ static-refᵐ fsA , ef-ref npM ⟩
  meta-elab-error-free (static-assign fsL fsM) fsΓᵐ (meta-assign elabL elabM B≲A)
    with meta-elab-error-free fsL fsΓᵐ elabL | meta-elab-error-free fsM fsΓᵐ elabM
  ... | ⟨ static-refᵐ fsA , npL ⟩ | ⟨ fsB , npM ⟩ =
    ⟨ static-baseᵐ , ef-assign npL (ef-cast npM (coerceᵐ-error-free fsB fsA B≲A)) ⟩
  meta-elab-error-free (static-assign fsL fsM) fsΓᵐ (meta-assign⋆ elabL elabM)
    with meta-elab-error-free fsL fsΓᵐ elabL
  ... | ⟨ () , _ ⟩
  meta-elab-error-free (static-deref fsM) fsΓᵐ (meta-deref elabM)
    with meta-elab-error-free fsM fsΓᵐ elabM
  ... | ⟨ static-refᵐ fsA , npM ⟩ = ⟨ fsA , ef-deref npM ⟩
  meta-elab-error-free (static-deref fsM) fsΓᵐ (meta-deref⋆ elabM)
    with meta-elab-error-free fsM fsΓᵐ elabM
  ... | ⟨ () , _ ⟩
