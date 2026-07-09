module LambdaAlphaRefStar.Theories.SpaceEfficiency.Proofs.PreserveOK where

open import Data.Bool using (true; false)
open import Data.List using ([]; _∷_; _∷ʳ_)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-trans; m≤n⇒m≤1+n)
open import Data.Product using (Σ-syntax; _×_) renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import Utils as U
import LambdaAlphaRefStar.Theories.Heap as H

open import LambdaAlphaRefStar.Theories.SpaceEfficiency.CCAlphaRefStarSyntaxAndTypeSystem
open import LambdaAlphaRefStar.Theories.SpaceEfficiency.CCAlphaRefStarSemantics
open import LambdaAlphaRefStar.Theories.SpaceEfficiency.Configuration
open import LambdaAlphaRefStar.Theories.SpaceEfficiency.AdjacentCastOK public


≤1⇒≤2 : ∀ {n} → n ≤ 1 → n ≤ 2
≤1⇒≤2 = m≤n⇒m≤1+n

cast-pres-ok : ∀ {M c n d}
  → n ∣ d ⊢ᵐ M ok
  → n ≤ 1
  → suc n ∣ d ⊢ᵐ M ⟨ c ⟩ ok
cast-pres-ok {d = true} Mok n≤1 = castdelayedOK Mok n≤1
cast-pres-ok {d = false} Mok n≤1 = castOK Mok (≤1⇒≤2 n≤1)

data ⊢_ok : Heap → Set where

  μok-[] :
      ----------------
      ⊢ [] ok

  μok-∷ : ∀ {μ V n}
    → Value V
    → n ∣ false ⊢ᵐ V ok
    → ⊢ μ ok
      -----------------------
    → ⊢ (V ∷ μ) ok

heap-values-ok-lookup : ∀ {μ a V}
  → ⊢ μ ok
  → U._∋_⦂_ μ a V
    ---------------------------------------------------
  → Value V × Σ[ n ∈ ℕ ] n ∣ false ⊢ᵐ V ok
heap-values-ok-lookup (μok-∷ value Vok μok) U.here =
  ⟨ value , ⟨ _ , Vok ⟩ ⟩
heap-values-ok-lookup (μok-∷ value Vok μok) (U.there lookup) =
  heap-values-ok-lookup μok lookup

heap-values-ok-extend : ∀ {μ V n}
  → ⊢ μ ok
  → Value V
  → n ∣ false ⊢ᵐ V ok
    -----------------------------
  → ⊢ (μ ∷ʳ V) ok
heap-values-ok-extend μok-[] value Vok =
  μok-∷ value Vok μok-[]
heap-values-ok-extend (μok-∷ value Wok μok) value′ Vok =
  μok-∷ value Wok (heap-values-ok-extend μok value′ Vok)

heap-values-ok-update : ∀ {μ μ′ a V n}
  → ⊢ μ ok
  → H._⟦_↦_⟧=_ μ a V μ′
  → Value V
  → n ∣ false ⊢ᵐ V ok
    --------------------
  → ⊢ μ′ ok
heap-values-ok-update (μok-∷ value Wok μok) H.here value′ Vok =
  μok-∷ value′ Vok μok
heap-values-ok-update (μok-∷ value Wok μok) (H.there μ↦μ′) value′ Vok =
  μok-∷ value Wok (heap-values-ok-update μok μ↦μ′ value′ Vok)

code-plug-ok-inversion : ∀ {F M d}
  → d ⊢ᵒ plugᵒ F M ok
    -------------------
  → d ⊢ᵒ M ok
code-plug-ok-inversion {F = □· Mᵒ} (appᵒOK Lok Mok) = Lok
code-plug-ok-inversion {F = (Vᵒ ·□) value} (appᵒOK Lok Mok) = Mok

meta-plug-ok-inversion : ∀ {F M n}
  → n ∣ false ⊢ᵐ plugᵐ F M ok
    --------------------------------
  → Σ[ m ∈ ℕ ] m ∣ false ⊢ᵐ M ok
meta-plug-ok-inversion {F = □· M} (appᵐOK {n = n} Mok Nok) =
  ⟨ n , Mok ⟩
meta-plug-ok-inversion {F = (V ·□) value} (appᵐOK {m = m} Vok Mok) =
  ⟨ m , Mok ⟩
meta-plug-ok-inversion {F = ref□} (refOK {n = n} Mok) =
  ⟨ n , Mok ⟩
meta-plug-ok-inversion {F = □:= M} (assignOK {n = n} Lok Mok) =
  ⟨ n , Lok ⟩
meta-plug-ok-inversion {F = (V :=□) value} (assignOK {m = m} Vok Mok) =
  ⟨ m , Mok ⟩
meta-plug-ok-inversion {F = !□} (derefOK {n = n} Mok) =
  ⟨ n , Mok ⟩
meta-plug-ok-inversion {F = □·[ e ]} (ecAppOK {n = n} Mok) =
  ⟨ n , Mok ⟩
meta-plug-ok-inversion {F = □●} (subElimOK {n = n} Mok) =
  ⟨ n , Mok ⟩
meta-plug-ok-inversion {F = □★ ℓ} (subElimDynOK {n = n} Mok) =
  ⟨ n , Mok ⟩

mutual

  preserve-heap-values-okᵒ : ∀ {C₁ C₂ e}
    → ⊢ (C₁ .μ) ok
    → false ⊢ᵒ C₁ .M ok
    → C₁ ∣ e —→ᵒ C₂
      ----------------------
    → ⊢ (C₂ .μ) ok
  preserve-heap-values-okᵒ μok C₁ok (ξ-code Fᵒ Mᵒ—→Nᵒ) =
    preserve-heap-values-okᵒ μok (code-plug-ok-inversion {F = Fᵒ} C₁ok) Mᵒ—→Nᵒ
  preserve-heap-values-okᵒ μok C₁ok (ξ-code-blame Fᵒ) = μok
  preserve-heap-values-okᵒ μok (spliceOK Mok) (ξ-splice M—→N) =
    preserve-heap-values-okᵐ μok Mok M—→N
  preserve-heap-values-okᵒ μok C₁ok splice-blame = μok
  preserve-heap-values-okᵒ μok C₁ok (splice-β value) = μok
  preserve-heap-values-okᵒ μok C₁ok (splice-sub value) = μok
  preserve-heap-values-okᵒ μok C₁ok code-λ = μok
  preserve-heap-values-okᵒ μok (absValᵒOK Nok) (ξ-code-λ̅ Mᵒ—→Nᵒ) =
    preserve-heap-values-okᵒ μok Nok Mᵒ—→Nᵒ
  preserve-heap-values-okᵒ μok C₁ok ξ-code-λ̅-blame = μok

  preserve-heap-values-okᵐ : ∀ {ctx C₁ C₂ n}
    → ⊢ (C₁ .μ) ok
    → n ∣ false ⊢ᵐ C₁ .M ok
    → ctx / C₁ —→ᵐ C₂
      ----------------------
    → ⊢ (C₂ .μ) ok
  preserve-heap-values-okᵐ μok C₁ok (ξ-meta F M—→N)
    with meta-plug-ok-inversion {F = F} C₁ok
  ... | ⟨ m , Mok ⟩ =
    preserve-heap-values-okᵐ μok Mok M—→N
  preserve-heap-values-okᵐ μok (castOK Mok n≤2) (ξ-cast M—→N) =
    preserve-heap-values-okᵐ μok Mok M—→N
  preserve-heap-values-okᵐ μok C₁ok (ξ-meta-blame F) = μok
  preserve-heap-values-okᵐ μok (quoteOK Mok) (ξ-quote Mᵒ—→Nᵒ) =
    preserve-heap-values-okᵒ μok Mok Mᵒ—→Nᵒ
  preserve-heap-values-okᵐ μok C₁ok quote-blame = μok
  preserve-heap-values-okᵐ μok C₁ok (β value) = μok
  preserve-heap-values-okᵐ μok C₁ok (β-cast raw value) = μok
  preserve-heap-values-okᵐ μok C₁ok Λ-β = μok
  preserve-heap-values-okᵐ μok C₁ok (Λ-β-cast raw) = μok
  preserve-heap-values-okᵐ μok C₁ok sub-β = μok
  preserve-heap-values-okᵐ μok C₁ok (sub-β-cast raw) = μok
  preserve-heap-values-okᵐ μok C₁ok (sub-cast-success raw e₁<:e₂) = μok
  preserve-heap-values-okᵐ μok C₁ok (sub-cast-sub-fail raw ¬e₁<:e₂) = μok
  preserve-heap-values-okᵐ μok C₁ok (sub-cast-fail raw ground ¬G⦊e₁<:e₂) = μok
  preserve-heap-values-okᵐ μok (refOK Vok) (ref value) =
    heap-values-ok-extend μok value Vok
  preserve-heap-values-okᵐ μok C₁ok (deref lookup) = μok
  preserve-heap-values-okᵐ μok (assignOK addrOK Vok) (assign value μ↦μ′) =
    heap-values-ok-update μok μ↦μ′ value Vok
  preserve-heap-values-okᵐ μok C₁ok (assign-cast value) = μok
  preserve-heap-values-okᵐ μok C₁ok deref-cast = μok
  preserve-heap-values-okᵐ μok C₁ok (cast-compose raw) = μok
  preserve-heap-values-okᵐ μok C₁ok (cast-id⋆ raw) = μok
  preserve-heap-values-okᵐ μok C₁ok (cast-idι raw) = μok
  preserve-heap-values-okᵐ μok C₁ok (cast-blame raw) = μok


≤2+n : ∀ n → n ≤ 2 + n
≤2+n zero = z≤n
≤2+n (suc n) = s≤s (≤2+n n)

≤2+suc : ∀ n → n ≤ 2 + suc n
≤2+suc n = ≤-trans (≤2+n n) (m≤n⇒m≤1+n ≤-refl)

mutual

  weaken-okᵒ : ∀ {M}
    → true ⊢ᵒ M ok
      ----------------
    → false ⊢ᵒ M ok
  weaken-okᵒ (spliceOK Mok) = spliceOK (weaken-okᵐ Mok)
  weaken-okᵒ constᵒOK = constᵒOK
  weaken-okᵒ varᵒOK = varᵒOK
  weaken-okᵒ (absᵒOK Nok) = absᵒOK (weaken-okᵒ Nok)
  weaken-okᵒ (absValᵒOK Nok) = absValᵒOK (weaken-okᵒ Nok)
  weaken-okᵒ (appᵒOK Lok Mok) = appᵒOK (weaken-okᵒ Lok) (weaken-okᵒ Mok)
  weaken-okᵒ blameᵒOK = blameᵒOK

  weaken-okᵐ : ∀ {M n}
    → n ∣ true ⊢ᵐ M ok
      --------------------
    → n ∣ false ⊢ᵐ M ok
  weaken-okᵐ (castdelayedOK Mok n≤1) =
    castOK (weaken-okᵐ Mok) (≤1⇒≤2 n≤1)
  weaken-okᵐ constᵐOK = constᵐOK
  weaken-okᵐ varᵐOK = varᵐOK
  weaken-okᵐ addrOK = addrOK
  weaken-okᵐ (absᵐOK Mok) = absᵐOK Mok
  weaken-okᵐ (appᵐOK Lok Mok) = appᵐOK (weaken-okᵐ Lok) (weaken-okᵐ Mok)
  weaken-okᵐ (ecAbsOK Mok) = ecAbsOK Mok
  weaken-okᵐ (ecAppOK Mok) = ecAppOK (weaken-okᵐ Mok)
  weaken-okᵐ (subIntroOK Mok) = subIntroOK Mok
  weaken-okᵐ (subElimOK Mok) = subElimOK (weaken-okᵐ Mok)
  weaken-okᵐ (subElimDynOK Mok) = subElimDynOK (weaken-okᵐ Mok)
  weaken-okᵐ (quoteOK Mok) = quoteOK (weaken-okᵒ Mok)
  weaken-okᵐ (refOK Mok) = refOK (weaken-okᵐ Mok)
  weaken-okᵐ (assignOK Lok Mok) = assignOK (weaken-okᵐ Lok) (weaken-okᵐ Mok)
  weaken-okᵐ (derefOK Mok) = derefOK (weaken-okᵐ Mok)
  weaken-okᵐ blameOK = blameOK

delayed-ok≤2 : ∀ {M n}
  → n ∣ true ⊢ᵐ M ok
    ------------------
  → n ≤ 2
delayed-ok≤2 (castdelayedOK Mok n≤1) = s≤s n≤1
delayed-ok≤2 constᵐOK = z≤n
delayed-ok≤2 varᵐOK = s≤s z≤n
delayed-ok≤2 addrOK = z≤n
delayed-ok≤2 (absᵐOK Mok) = z≤n
delayed-ok≤2 (appᵐOK Lok Mok) = z≤n
delayed-ok≤2 (ecAbsOK Mok) = z≤n
delayed-ok≤2 (ecAppOK Mok) = z≤n
delayed-ok≤2 (subIntroOK Mok) = z≤n
delayed-ok≤2 (subElimOK Mok) = z≤n
delayed-ok≤2 (subElimDynOK Mok) = z≤n
delayed-ok≤2 (quoteOK Mok) = z≤n
delayed-ok≤2 (refOK Mok) = z≤n
delayed-ok≤2 (assignOK Lok Mok) = z≤n
delayed-ok≤2 (derefOK Mok) = z≤n
delayed-ok≤2 blameOK = z≤n

raw-value-ok≤0 : ∀ {U n}
  → RawValue U
  → n ∣ false ⊢ᵐ U ok
    ------------------
  → n ≤ 0
raw-value-ok≤0 U-const constᵐOK = z≤n
raw-value-ok≤0 U-addr addrOK = z≤n
raw-value-ok≤0 U-ƛ (absᵐOK Mok) = z≤n
raw-value-ok≤0 U-Λ (ecAbsOK Mok) = z≤n
raw-value-ok≤0 (U-quote valueᵒ) (quoteOK Mok) = z≤n
raw-value-ok≤0 U-sub (subIntroOK Mok) = z≤n

value-ok≤1 : ∀ {V n}
  → Value V
  → n ∣ false ⊢ᵐ V ok
    ------------------
  → n ≤ 1
value-ok≤1 (V-raw raw) Vok =
  m≤n⇒m≤1+n (raw-value-ok≤0 raw Vok)
value-ok≤1 (V-cast raw inert) (castOK Uok n≤2) =
  s≤s (raw-value-ok≤0 raw Uok)

code-plug-ok : ∀ {F M N}
  → false ⊢ᵒ plugᵒ F M ok
  → false ⊢ᵒ N ok
    ---------------------------
  → false ⊢ᵒ plugᵒ F N ok
code-plug-ok {F = □· Mᵒ} (appᵒOK Lok Mok) Nok = appᵒOK Nok Mok
code-plug-ok {F = (Vᵒ ·□) value} (appᵒOK Vok Mok) Nok = appᵒOK Vok Nok

meta-plug-ok : ∀ {F M N n k}
  → n ∣ false ⊢ᵐ plugᵐ F M ok
  → k ∣ false ⊢ᵐ N ok
    --------------------------------
  → 0 ∣ false ⊢ᵐ plugᵐ F N ok
meta-plug-ok {F = □· M} (appᵐOK Lok Mok) Nok = appᵐOK Nok Mok
meta-plug-ok {F = (V ·□) value} (appᵐOK Vok Mok) Nok = appᵐOK Vok Nok
meta-plug-ok {F = ref□} (refOK Mok) Nok = refOK Nok
meta-plug-ok {F = □:= M} (assignOK Lok Mok) Nok = assignOK Nok Mok
meta-plug-ok {F = (V :=□) value} (assignOK Vok Mok) Nok = assignOK Vok Nok
meta-plug-ok {F = !□} (derefOK Mok) Nok = derefOK Nok
meta-plug-ok {F = □·[ e ]} (ecAppOK Mok) Nok = ecAppOK Nok
meta-plug-ok {F = □●} (subElimOK Mok) Nok = subElimOK Nok
meta-plug-ok {F = □★ ℓ} (subElimDynOK Mok) Nok = subElimDynOK Nok

meta-plug-ok0 : ∀ {F M n}
  → n ∣ false ⊢ᵐ plugᵐ F M ok
    ---------------------------
  → n ≡ 0
meta-plug-ok0 {F = □· M} (appᵐOK Lok Mok) = refl
meta-plug-ok0 {F = (V ·□) value} (appᵐOK Vok Mok) = refl
meta-plug-ok0 {F = ref□} (refOK Mok) = refl
meta-plug-ok0 {F = □:= M} (assignOK Lok Mok) = refl
meta-plug-ok0 {F = (V :=□) value} (assignOK Vok Mok) = refl
meta-plug-ok0 {F = !□} (derefOK Mok) = refl
meta-plug-ok0 {F = □·[ e ]} (ecAppOK Mok) = refl
meta-plug-ok0 {F = □●} (subElimOK Mok) = refl
meta-plug-ok0 {F = □★ ℓ} (subElimDynOK Mok) = refl

red-any-ok0ᵐ : ∀ {C₁ C₂ n}
  → n ∣ false ⊢ᵐ C₁ .M ok
  → Any / C₁ —→ᵐ C₂
    ------------------------
  → n ≡ 0
red-any-ok0ᵐ C₁ok (ξ-meta F M—→N) = meta-plug-ok0 {F = F} C₁ok
red-any-ok0ᵐ C₁ok (ξ-meta-blame F) = meta-plug-ok0 {F = F} C₁ok
red-any-ok0ᵐ (quoteOK Mok) (ξ-quote Mᵒ—→Nᵒ) = refl
red-any-ok0ᵐ (quoteOK Mok) quote-blame = refl
red-any-ok0ᵐ (appᵐOK Lok Mok) (β value) = refl
red-any-ok0ᵐ (appᵐOK Lok Mok) (β-cast raw value) = refl
red-any-ok0ᵐ (ecAppOK Mok) Λ-β = refl
red-any-ok0ᵐ (ecAppOK Mok) (Λ-β-cast raw) = refl
red-any-ok0ᵐ (subElimOK Mok) sub-β = refl
red-any-ok0ᵐ (subElimOK Mok) (sub-β-cast raw) = refl
red-any-ok0ᵐ (subElimDynOK Mok) (sub-cast-success raw e₁<:e₂) = refl
red-any-ok0ᵐ (subElimDynOK Mok) (sub-cast-sub-fail raw ¬e₁<:e₂) = refl
red-any-ok0ᵐ (subElimDynOK Mok) (sub-cast-fail raw ground ¬G⦊e₁<:e₂) = refl
red-any-ok0ᵐ (refOK Mok) (ref value) = refl
red-any-ok0ᵐ (derefOK Mok) (deref lookup) = refl
red-any-ok0ᵐ (assignOK Lok Mok) (assign value μ↦μ′) = refl
red-any-ok0ᵐ (assignOK Lok Mok) (assign-cast value) = refl
red-any-ok0ᵐ (derefOK Mok) deref-cast = refl

mutual

  renᵐ-code-ok : ∀ {ρ M d}
    → d ⊢ᵒ M ok
      --------------------------
    → d ⊢ᵒ renᵐ-code ρ M ok
  renᵐ-code-ok constᵒOK = constᵒOK
  renᵐ-code-ok varᵒOK = varᵒOK
  renᵐ-code-ok (absᵒOK Mok) = absᵒOK (renᵐ-code-ok Mok)
  renᵐ-code-ok (absValᵒOK Mok) = absValᵒOK (renᵐ-code-ok Mok)
  renᵐ-code-ok (appᵒOK Lok Mok) = appᵒOK (renᵐ-code-ok Lok) (renᵐ-code-ok Mok)
  renᵐ-code-ok (spliceOK Mok) = spliceOK (renᵐ-meta-ok Mok)
  renᵐ-code-ok blameᵒOK = blameᵒOK

  renᵐ-meta-ok : ∀ {ρ M n d}
    → n ∣ d ⊢ᵐ M ok
      ------------------------------
    → n ∣ d ⊢ᵐ renᵐ-meta ρ M ok
  renᵐ-meta-ok (castdelayedOK Mok n≤1) = castdelayedOK (renᵐ-meta-ok Mok) n≤1
  renᵐ-meta-ok (castOK Mok n≤2) = castOK (renᵐ-meta-ok Mok) n≤2
  renᵐ-meta-ok constᵐOK = constᵐOK
  renᵐ-meta-ok varᵐOK = varᵐOK
  renᵐ-meta-ok addrOK = addrOK
  renᵐ-meta-ok (absᵐOK Mok) = absᵐOK (renᵐ-meta-ok Mok)
  renᵐ-meta-ok (appᵐOK Lok Mok) = appᵐOK (renᵐ-meta-ok Lok) (renᵐ-meta-ok Mok)
  renᵐ-meta-ok (ecAbsOK Mok) = ecAbsOK (renᵐ-meta-ok Mok)
  renᵐ-meta-ok (ecAppOK Mok) = ecAppOK (renᵐ-meta-ok Mok)
  renᵐ-meta-ok (subIntroOK Mok) = subIntroOK (renᵐ-meta-ok Mok)
  renᵐ-meta-ok (subElimOK Mok) = subElimOK (renᵐ-meta-ok Mok)
  renᵐ-meta-ok (subElimDynOK Mok) = subElimDynOK (renᵐ-meta-ok Mok)
  renᵐ-meta-ok (quoteOK Mok) = quoteOK (renᵐ-code-ok Mok)
  renᵐ-meta-ok (refOK Mok) = refOK (renᵐ-meta-ok Mok)
  renᵐ-meta-ok (assignOK Lok Mok) = assignOK (renᵐ-meta-ok Lok) (renᵐ-meta-ok Mok)
  renᵐ-meta-ok (derefOK Mok) = derefOK (renᵐ-meta-ok Mok)
  renᵐ-meta-ok blameOK = blameOK

mutual

  renᵉ-code-ok : ∀ {ρ M d}
    → d ⊢ᵒ M ok
      --------------------------
    → d ⊢ᵒ renᵉ-code ρ M ok
  renᵉ-code-ok constᵒOK = constᵒOK
  renᵉ-code-ok varᵒOK = varᵒOK
  renᵉ-code-ok (absᵒOK Mok) = absᵒOK (renᵉ-code-ok Mok)
  renᵉ-code-ok (absValᵒOK Mok) = absValᵒOK (renᵉ-code-ok Mok)
  renᵉ-code-ok (appᵒOK Lok Mok) = appᵒOK (renᵉ-code-ok Lok) (renᵉ-code-ok Mok)
  renᵉ-code-ok (spliceOK Mok) = spliceOK (renᵉ-meta-ok Mok)
  renᵉ-code-ok blameᵒOK = blameᵒOK

  renᵉ-meta-ok : ∀ {ρ M n d}
    → n ∣ d ⊢ᵐ M ok
      ------------------------------
    → n ∣ d ⊢ᵐ renᵉ-meta ρ M ok
  renᵉ-meta-ok (castdelayedOK Mok n≤1) = castdelayedOK (renᵉ-meta-ok Mok) n≤1
  renᵉ-meta-ok (castOK Mok n≤2) = castOK (renᵉ-meta-ok Mok) n≤2
  renᵉ-meta-ok constᵐOK = constᵐOK
  renᵉ-meta-ok varᵐOK = varᵐOK
  renᵉ-meta-ok addrOK = addrOK
  renᵉ-meta-ok (absᵐOK Mok) = absᵐOK (renᵉ-meta-ok Mok)
  renᵉ-meta-ok (appᵐOK Lok Mok) = appᵐOK (renᵉ-meta-ok Lok) (renᵉ-meta-ok Mok)
  renᵉ-meta-ok (ecAbsOK Mok) = ecAbsOK (renᵉ-meta-ok Mok)
  renᵉ-meta-ok (ecAppOK Mok) = ecAppOK (renᵉ-meta-ok Mok)
  renᵉ-meta-ok (subIntroOK Mok) = subIntroOK (renᵉ-meta-ok Mok)
  renᵉ-meta-ok (subElimOK Mok) = subElimOK (renᵉ-meta-ok Mok)
  renᵉ-meta-ok (subElimDynOK Mok) = subElimDynOK (renᵉ-meta-ok Mok)
  renᵉ-meta-ok (quoteOK Mok) = quoteOK (renᵉ-code-ok Mok)
  renᵉ-meta-ok (refOK Mok) = refOK (renᵉ-meta-ok Mok)
  renᵉ-meta-ok (assignOK Lok Mok) = assignOK (renᵉ-meta-ok Lok) (renᵉ-meta-ok Mok)
  renᵉ-meta-ok (derefOK Mok) = derefOK (renᵉ-meta-ok Mok)
  renᵉ-meta-ok blameOK = blameOK

mutual

  renᵒ-code-ok : ∀ {ρ M d}
    → d ⊢ᵒ M ok
      --------------------------
    → d ⊢ᵒ renᵒ-code ρ M ok
  renᵒ-code-ok constᵒOK = constᵒOK
  renᵒ-code-ok varᵒOK = varᵒOK
  renᵒ-code-ok (absᵒOK Mok) = absᵒOK (renᵒ-code-ok Mok)
  renᵒ-code-ok (absValᵒOK Mok) = absValᵒOK (renᵒ-code-ok Mok)
  renᵒ-code-ok (appᵒOK Lok Mok) = appᵒOK (renᵒ-code-ok Lok) (renᵒ-code-ok Mok)
  renᵒ-code-ok (spliceOK Mok) = spliceOK (renᵒ-meta-ok Mok)
  renᵒ-code-ok blameᵒOK = blameᵒOK

  renᵒ-meta-ok : ∀ {ρ M n d}
    → n ∣ d ⊢ᵐ M ok
      ------------------------------
    → n ∣ d ⊢ᵐ renᵒ-meta ρ M ok
  renᵒ-meta-ok (castdelayedOK Mok n≤1) = castdelayedOK (renᵒ-meta-ok Mok) n≤1
  renᵒ-meta-ok (castOK Mok n≤2) = castOK (renᵒ-meta-ok Mok) n≤2
  renᵒ-meta-ok constᵐOK = constᵐOK
  renᵒ-meta-ok varᵐOK = varᵐOK
  renᵒ-meta-ok addrOK = addrOK
  renᵒ-meta-ok (absᵐOK Mok) = absᵐOK (renᵒ-meta-ok Mok)
  renᵒ-meta-ok (appᵐOK Lok Mok) = appᵐOK (renᵒ-meta-ok Lok) (renᵒ-meta-ok Mok)
  renᵒ-meta-ok (ecAbsOK Mok) = ecAbsOK (renᵒ-meta-ok Mok)
  renᵒ-meta-ok (ecAppOK Mok) = ecAppOK (renᵒ-meta-ok Mok)
  renᵒ-meta-ok (subIntroOK Mok) = subIntroOK (renᵒ-meta-ok Mok)
  renᵒ-meta-ok (subElimOK Mok) = subElimOK (renᵒ-meta-ok Mok)
  renᵒ-meta-ok (subElimDynOK Mok) = subElimDynOK (renᵒ-meta-ok Mok)
  renᵒ-meta-ok (quoteOK Mok) = quoteOK (renᵒ-code-ok Mok)
  renᵒ-meta-ok (refOK Mok) = refOK (renᵒ-meta-ok Mok)
  renᵒ-meta-ok (assignOK Lok Mok) = assignOK (renᵒ-meta-ok Lok) (renᵒ-meta-ok Mok)
  renᵒ-meta-ok (derefOK Mok) = derefOK (renᵒ-meta-ok Mok)
  renᵒ-meta-ok blameOK = blameOK

codevalue-strengthen-ok : ∀ {Vᵒ}
  → CodeValue Vᵒ
  → false ⊢ᵒ Vᵒ ok
    ----------------
  → true ⊢ᵒ Vᵒ ok
codevalue-strengthen-ok is-const constᵒOK = constᵒOK
codevalue-strengthen-ok is-var varᵒOK = varᵒOK
codevalue-strengthen-ok (is-lamᵒ-val valueᵒ) (absValᵒOK Vᵒok) =
  absValᵒOK (codevalue-strengthen-ok valueᵒ Vᵒok)
codevalue-strengthen-ok (is-app valueL valueM) (appᵒOK Lok Mok) =
  appᵒOK (codevalue-strengthen-ok valueL Lok) (codevalue-strengthen-ok valueM Mok)

raw-value-strengthen-ok : ∀ {U n}
  → RawValue U
  → n ∣ false ⊢ᵐ U ok
    --------------------
  → n ∣ true ⊢ᵐ U ok
raw-value-strengthen-ok U-const constᵐOK = constᵐOK
raw-value-strengthen-ok U-addr addrOK = addrOK
raw-value-strengthen-ok U-ƛ (absᵐOK Uok) = absᵐOK Uok
raw-value-strengthen-ok U-Λ (ecAbsOK Uok) = ecAbsOK Uok
raw-value-strengthen-ok (U-quote valueᵒ) (quoteOK Uok) =
  quoteOK (codevalue-strengthen-ok valueᵒ Uok)
raw-value-strengthen-ok U-sub (subIntroOK Uok) = subIntroOK Uok

value-strengthen-ok : ∀ {V n}
  → Value V
  → n ∣ false ⊢ᵐ V ok
    --------------------
  → n ∣ true ⊢ᵐ V ok
value-strengthen-ok (V-raw raw) Vok =
  raw-value-strengthen-ok raw Vok
value-strengthen-ok (V-cast raw inert) (castOK Uok n≤2) =
  castdelayedOK
    (raw-value-strengthen-ok raw Uok)
    (m≤n⇒m≤1+n (raw-value-ok≤0 raw Uok))

SubstMetaOK : SubstMeta → Set
SubstMetaOK σ =
  ∀ x → Σ[ m ∈ ℕ ] (m ∣ true ⊢ᵐ σ x ok × m ≤ 1)

subst-ok-extsᵐ : ∀ {σ}
  → SubstMetaOK σ
    ----------------------
  → SubstMetaOK (extsᵐ σ)
subst-ok-extsᵐ σok zero =
  ⟨ suc zero , ⟨ varᵐOK , s≤s z≤n ⟩ ⟩
subst-ok-extsᵐ σok (suc x)
  with σok x
... | ⟨ m , ⟨ σxok , m≤1 ⟩ ⟩ =
  ⟨ m , ⟨ renᵐ-meta-ok σxok , m≤1 ⟩ ⟩

subst-ok-⇑ᵉˢ : ∀ {σ}
  → SubstMetaOK σ
    ----------------------
  → SubstMetaOK (⇑ᵉˢ σ)
subst-ok-⇑ᵉˢ σok x
  with σok x
... | ⟨ m , ⟨ σxok , m≤1 ⟩ ⟩ =
  ⟨ m , ⟨ renᵉ-meta-ok σxok , m≤1 ⟩ ⟩

subst-ok-⇑ᵒˢ : ∀ {σ}
  → SubstMetaOK σ
    ----------------------
  → SubstMetaOK (⇑ᵒˢ σ)
subst-ok-⇑ᵒˢ σok x
  with σok x
... | ⟨ m , ⟨ σxok , m≤1 ⟩ ⟩ =
  ⟨ m , ⟨ renᵒ-meta-ok σxok , m≤1 ⟩ ⟩

mutual

  substᵐ-code-ok : ∀ {σ M d}
    → SubstMetaOK σ
    → d ⊢ᵒ M ok
      -----------------------------
    → d ⊢ᵒ substᵐ-code σ M ok
  substᵐ-code-ok σok constᵒOK = constᵒOK
  substᵐ-code-ok σok varᵒOK = varᵒOK
  substᵐ-code-ok σok (absᵒOK Mok) =
    absᵒOK (substᵐ-code-ok (subst-ok-⇑ᵒˢ (subst-ok-⇑ᵉˢ σok)) Mok)
  substᵐ-code-ok σok (absValᵒOK Mok) =
    absValᵒOK (substᵐ-code-ok σok Mok)
  substᵐ-code-ok σok (appᵒOK Lok Mok) =
    appᵒOK (substᵐ-code-ok σok Lok) (substᵐ-code-ok σok Mok)
  substᵐ-code-ok σok (spliceOK Mok)
    with substᵐ-meta-ok σok Mok
  ... | ⟨ k , ⟨ σMok , k≤n ⟩ ⟩ =
    spliceOK σMok
  substᵐ-code-ok σok blameᵒOK = blameᵒOK

  substᵐ-meta-ok : ∀ {σ M n d}
    → SubstMetaOK σ
    → n ∣ d ⊢ᵐ M ok
      -------------------------------------------------------
    → Σ[ k ∈ ℕ ] (k ∣ d ⊢ᵐ substᵐ-meta σ M ok × k ≤ n)
  substᵐ-meta-ok σok (castdelayedOK Mok n≤1)
    with substᵐ-meta-ok σok Mok
  ... | ⟨ k , ⟨ σMok , k≤n ⟩ ⟩ =
    ⟨ suc k , ⟨ castdelayedOK σMok (≤-trans k≤n n≤1) , s≤s k≤n ⟩ ⟩
  substᵐ-meta-ok σok (castOK Mok n≤2)
    with substᵐ-meta-ok σok Mok
  ... | ⟨ k , ⟨ σMok , k≤n ⟩ ⟩ =
    ⟨ suc k , ⟨ castOK σMok (≤-trans k≤n n≤2) , s≤s k≤n ⟩ ⟩
  substᵐ-meta-ok σok constᵐOK =
    ⟨ zero , ⟨ constᵐOK , z≤n ⟩ ⟩
  substᵐ-meta-ok σok (varᵐOK {x = x} {delayed = true}) =
    σok x
  substᵐ-meta-ok σok (varᵐOK {x = x} {delayed = false})
    with σok x
  ... | ⟨ m , ⟨ σxok , m≤1 ⟩ ⟩ =
    ⟨ m , ⟨ weaken-okᵐ σxok , m≤1 ⟩ ⟩
  substᵐ-meta-ok σok addrOK =
    ⟨ zero , ⟨ addrOK , z≤n ⟩ ⟩
  substᵐ-meta-ok σok (absᵐOK Mok)
    with substᵐ-meta-ok (subst-ok-extsᵐ σok) Mok
  ... | ⟨ k , ⟨ σMok , k≤n ⟩ ⟩ =
    ⟨ zero , ⟨ absᵐOK σMok , z≤n ⟩ ⟩
  substᵐ-meta-ok σok (appᵐOK Lok Mok)
    with substᵐ-meta-ok σok Lok | substᵐ-meta-ok σok Mok
  ... | ⟨ l , ⟨ σLok , l≤n ⟩ ⟩ | ⟨ m , ⟨ σMok , m≤n ⟩ ⟩ =
    ⟨ zero , ⟨ appᵐOK σLok σMok , z≤n ⟩ ⟩
  substᵐ-meta-ok σok (ecAbsOK Mok)
    with substᵐ-meta-ok (subst-ok-⇑ᵉˢ σok) Mok
  ... | ⟨ k , ⟨ σMok , k≤n ⟩ ⟩ =
    ⟨ zero , ⟨ ecAbsOK σMok , z≤n ⟩ ⟩
  substᵐ-meta-ok σok (ecAppOK Mok)
    with substᵐ-meta-ok σok Mok
  ... | ⟨ k , ⟨ σMok , k≤n ⟩ ⟩ =
    ⟨ zero , ⟨ ecAppOK σMok , z≤n ⟩ ⟩
  substᵐ-meta-ok σok (subIntroOK Mok)
    with substᵐ-meta-ok σok Mok
  ... | ⟨ k , ⟨ σMok , k≤n ⟩ ⟩ =
    ⟨ zero , ⟨ subIntroOK σMok , z≤n ⟩ ⟩
  substᵐ-meta-ok σok (subElimOK Mok)
    with substᵐ-meta-ok σok Mok
  ... | ⟨ k , ⟨ σMok , k≤n ⟩ ⟩ =
    ⟨ zero , ⟨ subElimOK σMok , z≤n ⟩ ⟩
  substᵐ-meta-ok σok (subElimDynOK Mok)
    with substᵐ-meta-ok σok Mok
  ... | ⟨ k , ⟨ σMok , k≤n ⟩ ⟩ =
    ⟨ zero , ⟨ subElimDynOK σMok , z≤n ⟩ ⟩
  substᵐ-meta-ok σok (quoteOK Mok) =
    ⟨ zero , ⟨ quoteOK (substᵐ-code-ok σok Mok) , z≤n ⟩ ⟩
  substᵐ-meta-ok σok (refOK Mok)
    with substᵐ-meta-ok σok Mok
  ... | ⟨ k , ⟨ σMok , k≤n ⟩ ⟩ =
    ⟨ zero , ⟨ refOK σMok , z≤n ⟩ ⟩
  substᵐ-meta-ok σok (assignOK Lok Mok)
    with substᵐ-meta-ok σok Lok | substᵐ-meta-ok σok Mok
  ... | ⟨ l , ⟨ σLok , l≤n ⟩ ⟩ | ⟨ m , ⟨ σMok , m≤n ⟩ ⟩ =
    ⟨ zero , ⟨ assignOK σLok σMok , z≤n ⟩ ⟩
  substᵐ-meta-ok σok (derefOK Mok)
    with substᵐ-meta-ok σok Mok
  ... | ⟨ k , ⟨ σMok , k≤n ⟩ ⟩ =
    ⟨ zero , ⟨ derefOK σMok , z≤n ⟩ ⟩
  substᵐ-meta-ok σok blameOK =
    ⟨ zero , ⟨ blameOK , z≤n ⟩ ⟩

single-subst-meta-ok : ∀ {V m}
  → m ∣ false ⊢ᵐ V ok
  → Value V
    -------------------------------
  → SubstMetaOK (V •ᵐₛ idsᵐ)
single-subst-meta-ok Vok value zero =
  ⟨ _ , ⟨ value-strengthen-ok value Vok , value-ok≤1 value Vok ⟩ ⟩
single-subst-meta-ok Vok value (suc x) =
  ⟨ suc zero , ⟨ varᵐOK , s≤s z≤n ⟩ ⟩

subst-meta-ok : ∀ {N V n m}
  → n ∣ true ⊢ᵐ N ok
  → m ∣ false ⊢ᵐ V ok
  → Value V
    -----------------------------------------------
  → Σ[ k ∈ ℕ ] (k ∣ false ⊢ᵐ N [ V ]ᵐ ok × k ≤ n)
subst-meta-ok Nok Vok value
  with substᵐ-meta-ok (single-subst-meta-ok Vok value) Nok
... | ⟨ k , ⟨ NVok , k≤n ⟩ ⟩ =
  ⟨ k , ⟨ weaken-okᵐ NVok , k≤n ⟩ ⟩

mutual

  substᵉ-code-ok : ∀ {σ M d}
    → d ⊢ᵒ M ok
      -----------------------------
    → d ⊢ᵒ substᵉ-code σ M ok
  substᵉ-code-ok constᵒOK = constᵒOK
  substᵉ-code-ok varᵒOK = varᵒOK
  substᵉ-code-ok (absᵒOK Mok) = absᵒOK (substᵉ-code-ok Mok)
  substᵉ-code-ok (absValᵒOK Mok) = absValᵒOK (substᵉ-code-ok Mok)
  substᵉ-code-ok (appᵒOK Lok Mok) = appᵒOK (substᵉ-code-ok Lok) (substᵉ-code-ok Mok)
  substᵉ-code-ok (spliceOK Mok) = spliceOK (substᵉ-meta-ok Mok)
  substᵉ-code-ok blameᵒOK = blameᵒOK

  substᵉ-meta-ok : ∀ {σ M n d}
    → n ∣ d ⊢ᵐ M ok
      ---------------------------------
    → n ∣ d ⊢ᵐ substᵉ-meta σ M ok
  substᵉ-meta-ok (castdelayedOK Mok n≤1) =
    castdelayedOK (substᵉ-meta-ok Mok) n≤1
  substᵉ-meta-ok (castOK Mok n≤2) =
    castOK (substᵉ-meta-ok Mok) n≤2
  substᵉ-meta-ok constᵐOK = constᵐOK
  substᵉ-meta-ok varᵐOK = varᵐOK
  substᵉ-meta-ok addrOK = addrOK
  substᵉ-meta-ok (absᵐOK Mok) = absᵐOK (substᵉ-meta-ok Mok)
  substᵉ-meta-ok (appᵐOK Lok Mok) =
    appᵐOK (substᵉ-meta-ok Lok) (substᵉ-meta-ok Mok)
  substᵉ-meta-ok (ecAbsOK Mok) = ecAbsOK (substᵉ-meta-ok Mok)
  substᵉ-meta-ok (ecAppOK Mok) = ecAppOK (substᵉ-meta-ok Mok)
  substᵉ-meta-ok (subIntroOK Mok) = subIntroOK (substᵉ-meta-ok Mok)
  substᵉ-meta-ok (subElimOK Mok) = subElimOK (substᵉ-meta-ok Mok)
  substᵉ-meta-ok (subElimDynOK Mok) = subElimDynOK (substᵉ-meta-ok Mok)
  substᵉ-meta-ok (quoteOK Mok) = quoteOK (substᵉ-code-ok Mok)
  substᵉ-meta-ok (refOK Mok) = refOK (substᵉ-meta-ok Mok)
  substᵉ-meta-ok (assignOK Lok Mok) =
    assignOK (substᵉ-meta-ok Lok) (substᵉ-meta-ok Mok)
  substᵉ-meta-ok (derefOK Mok) = derefOK (substᵉ-meta-ok Mok)
  substᵉ-meta-ok blameOK = blameOK

subst-ec-meta-ok : ∀ {M e n}
  → n ∣ true ⊢ᵐ M ok
    -----------------------------------------------
  → Σ[ k ∈ ℕ ] (k ∣ false ⊢ᵐ M [ e ]ᵉᵐ ok × k ≤ n)
subst-ec-meta-ok Mok =
  ⟨ _ , ⟨ weaken-okᵐ (substᵉ-meta-ok Mok) , ≤-refl ⟩ ⟩

subst-ec-code-ok : ∀ {M e}
  → false ⊢ᵒ M ok
    ------------------------------
  → false ⊢ᵒ M [ e ]ᵉᵒ ok
subst-ec-code-ok Mok = substᵉ-code-ok Mok

SubstCodeOK : SubstCode → Set
SubstCodeOK σ = ∀ {d} x → d ⊢ᵒ σ x ok

subst-ok-extsᵒ : ∀ {σ}
  → SubstCodeOK σ
    -----------------------
  → SubstCodeOK (extsᵒ σ)
subst-ok-extsᵒ σok zero = varᵒOK
subst-ok-extsᵒ σok (suc x) = renᵒ-code-ok (σok x)

mutual

  substᵒ-code-ok : ∀ {σ M d}
    → SubstCodeOK σ
    → d ⊢ᵒ M ok
      -----------------------------
    → d ⊢ᵒ substᵒ-code σ M ok
  substᵒ-code-ok σok constᵒOK = constᵒOK
  substᵒ-code-ok σok varᵒOK = σok _
  substᵒ-code-ok σok (absᵒOK Mok) =
    absᵒOK (substᵒ-code-ok (subst-ok-extsᵒ σok) Mok)
  substᵒ-code-ok σok (absValᵒOK Mok) =
    absValᵒOK (substᵒ-code-ok σok Mok)
  substᵒ-code-ok σok (appᵒOK Lok Mok) =
    appᵒOK (substᵒ-code-ok σok Lok) (substᵒ-code-ok σok Mok)
  substᵒ-code-ok σok (spliceOK Mok)
    with substᵒ-meta-ok σok Mok
  ... | ⟨ k , ⟨ σMok , k≤n ⟩ ⟩ =
    spliceOK σMok
  substᵒ-code-ok σok blameᵒOK = blameᵒOK

  substᵒ-meta-ok : ∀ {σ M n d}
    → SubstCodeOK σ
    → n ∣ d ⊢ᵐ M ok
      -------------------------------------------------------
    → Σ[ k ∈ ℕ ] (k ∣ d ⊢ᵐ substᵒ-meta σ M ok × k ≤ n)
  substᵒ-meta-ok σok (castdelayedOK Mok n≤1)
    with substᵒ-meta-ok σok Mok
  ... | ⟨ k , ⟨ σMok , k≤n ⟩ ⟩ =
    ⟨ suc k , ⟨ castdelayedOK σMok (≤-trans k≤n n≤1) , s≤s k≤n ⟩ ⟩
  substᵒ-meta-ok σok (castOK Mok n≤2)
    with substᵒ-meta-ok σok Mok
  ... | ⟨ k , ⟨ σMok , k≤n ⟩ ⟩ =
    ⟨ suc k , ⟨ castOK σMok (≤-trans k≤n n≤2) , s≤s k≤n ⟩ ⟩
  substᵒ-meta-ok σok constᵐOK =
    ⟨ zero , ⟨ constᵐOK , z≤n ⟩ ⟩
  substᵒ-meta-ok σok varᵐOK =
    ⟨ suc zero , ⟨ varᵐOK , ≤-refl ⟩ ⟩
  substᵒ-meta-ok σok addrOK =
    ⟨ zero , ⟨ addrOK , z≤n ⟩ ⟩
  substᵒ-meta-ok σok (absᵐOK Mok)
    with substᵒ-meta-ok σok Mok
  ... | ⟨ k , ⟨ σMok , k≤n ⟩ ⟩ =
    ⟨ zero , ⟨ absᵐOK σMok , z≤n ⟩ ⟩
  substᵒ-meta-ok σok (appᵐOK Lok Mok)
    with substᵒ-meta-ok σok Lok | substᵒ-meta-ok σok Mok
  ... | ⟨ l , ⟨ σLok , l≤n ⟩ ⟩ | ⟨ m , ⟨ σMok , m≤n ⟩ ⟩ =
    ⟨ zero , ⟨ appᵐOK σLok σMok , z≤n ⟩ ⟩
  substᵒ-meta-ok σok (ecAbsOK Mok)
    with substᵒ-meta-ok σok Mok
  ... | ⟨ k , ⟨ σMok , k≤n ⟩ ⟩ =
    ⟨ zero , ⟨ ecAbsOK σMok , z≤n ⟩ ⟩
  substᵒ-meta-ok σok (ecAppOK Mok)
    with substᵒ-meta-ok σok Mok
  ... | ⟨ k , ⟨ σMok , k≤n ⟩ ⟩ =
    ⟨ zero , ⟨ ecAppOK σMok , z≤n ⟩ ⟩
  substᵒ-meta-ok σok (subIntroOK Mok)
    with substᵒ-meta-ok σok Mok
  ... | ⟨ k , ⟨ σMok , k≤n ⟩ ⟩ =
    ⟨ zero , ⟨ subIntroOK σMok , z≤n ⟩ ⟩
  substᵒ-meta-ok σok (subElimOK Mok)
    with substᵒ-meta-ok σok Mok
  ... | ⟨ k , ⟨ σMok , k≤n ⟩ ⟩ =
    ⟨ zero , ⟨ subElimOK σMok , z≤n ⟩ ⟩
  substᵒ-meta-ok σok (subElimDynOK Mok)
    with substᵒ-meta-ok σok Mok
  ... | ⟨ k , ⟨ σMok , k≤n ⟩ ⟩ =
    ⟨ zero , ⟨ subElimDynOK σMok , z≤n ⟩ ⟩
  substᵒ-meta-ok σok (quoteOK Mok) =
    ⟨ zero , ⟨ quoteOK (substᵒ-code-ok σok Mok) , z≤n ⟩ ⟩
  substᵒ-meta-ok σok (refOK Mok)
    with substᵒ-meta-ok σok Mok
  ... | ⟨ k , ⟨ σMok , k≤n ⟩ ⟩ =
    ⟨ zero , ⟨ refOK σMok , z≤n ⟩ ⟩
  substᵒ-meta-ok σok (assignOK Lok Mok)
    with substᵒ-meta-ok σok Lok | substᵒ-meta-ok σok Mok
  ... | ⟨ l , ⟨ σLok , l≤n ⟩ ⟩ | ⟨ m , ⟨ σMok , m≤n ⟩ ⟩ =
    ⟨ zero , ⟨ assignOK σLok σMok , z≤n ⟩ ⟩
  substᵒ-meta-ok σok (derefOK Mok)
    with substᵒ-meta-ok σok Mok
  ... | ⟨ k , ⟨ σMok , k≤n ⟩ ⟩ =
    ⟨ zero , ⟨ derefOK σMok , z≤n ⟩ ⟩
  substᵒ-meta-ok σok blameOK =
    ⟨ zero , ⟨ blameOK , z≤n ⟩ ⟩

single-subst-code-ok : ∀ {y}
  → SubstCodeOK ((` y) •ᵒₛ idsᵒ)
single-subst-code-ok zero = varᵒOK
single-subst-code-ok (suc x) = varᵒOK

subst-code-var-code-ok : ∀ {M y}
  → false ⊢ᵒ M ok
    ----------------------------
  → false ⊢ᵒ M [ ` y ]ᵒ ok
subst-code-var-code-ok Mok = substᵒ-code-ok single-subst-code-ok Mok

mutual

  preserve-okᵒ : ∀ {C₁ C₂ e}
    → ⊢ (C₁ .μ) ok
    → false ⊢ᵒ C₁ .M ok
    → C₁ ∣ e —→ᵒ C₂
      -------------------
    → false ⊢ᵒ C₂ .M ok
  preserve-okᵒ μok C₁ok (ξ-code Fᵒ Mᵒ—→Nᵒ) =
    code-plug-ok {F = Fᵒ} C₁ok
      (preserve-okᵒ μok (code-plug-ok-inversion {F = Fᵒ} C₁ok) Mᵒ—→Nᵒ)
  preserve-okᵒ μok C₁ok (ξ-code-blame Fᵒ) = blameᵒOK
  preserve-okᵒ μok (spliceOK Mok) (ξ-splice M—→N)
    with preserve-okᵐ μok Mok M—→N
  ... | ⟨ m , ⟨ Nok , m≤2+n ⟩ ⟩ = spliceOK Nok
  preserve-okᵒ μok C₁ok splice-blame = blameᵒOK
  preserve-okᵒ μok (spliceOK (quoteOK Vᵒok)) (splice-β value) = Vᵒok
  preserve-okᵒ μok (spliceOK (castOK (quoteOK Vᵒok) n≤2)) (splice-sub value) = Vᵒok
  preserve-okᵒ μok (absᵒOK Nok) code-λ =
    absValᵒOK (subst-code-var-code-ok (subst-ec-code-ok Nok))
  preserve-okᵒ μok (absValᵒOK Nok) (ξ-code-λ̅ Mᵒ—→Nᵒ) =
    absValᵒOK (preserve-okᵒ μok Nok Mᵒ—→Nᵒ)
  preserve-okᵒ μok C₁ok ξ-code-λ̅-blame = blameᵒOK

  preserve-okᵐ : ∀ {ctx C₁ C₂ n}
    → ⊢ (C₁ .μ) ok
    → n ∣ false ⊢ᵐ C₁ .M ok
    → ctx / C₁ —→ᵐ C₂
      -----------------------------------------------------------
    → Σ[ m ∈ ℕ ] (m ∣ false ⊢ᵐ C₂ .M ok × m ≤ 2 + n)
  preserve-okᵐ μok C₁ok (ξ-meta F M—→N)
    with meta-plug-ok-inversion {F = F} C₁ok
  ... | ⟨ m , Mok ⟩
    with preserve-okᵐ μok Mok M—→N
  ... | ⟨ k , ⟨ Nok , k≤2+m ⟩ ⟩ =
    ⟨ zero , ⟨ meta-plug-ok {F = F} C₁ok Nok , z≤n ⟩ ⟩
  preserve-okᵐ μok (castOK Mok n≤2) (ξ-cast M—→N)
    with preserve-okᵐ μok Mok M—→N | red-any-ok0ᵐ Mok M—→N
  ... | ⟨ m , ⟨ Nok , m≤2+n ⟩ ⟩ | refl =
    ⟨ suc m , ⟨ castOK Nok m≤2+n , s≤s m≤2+n ⟩ ⟩
  preserve-okᵐ μok C₁ok (ξ-meta-blame F) =
    ⟨ zero , ⟨ blameOK , z≤n ⟩ ⟩
  preserve-okᵐ μok (quoteOK Mok) (ξ-quote Mᵒ—→Nᵒ) =
    ⟨ zero , ⟨ quoteOK (preserve-okᵒ μok Mok Mᵒ—→Nᵒ) , z≤n ⟩ ⟩
  preserve-okᵐ μok C₁ok quote-blame =
    ⟨ zero , ⟨ blameOK , z≤n ⟩ ⟩
  preserve-okᵐ μok (appᵐOK (absᵐOK Nok) Vok) (β value)
    with subst-meta-ok Nok Vok value
  ... | ⟨ k , ⟨ NVok , k≤n ⟩ ⟩ =
    ⟨ k , ⟨ NVok , ≤-trans k≤n (delayed-ok≤2 Nok) ⟩ ⟩
  preserve-okᵐ μok (appᵐOK (castOK Uok n≤2) Wok) (β-cast raw value) =
    let W≤1 = value-ok≤1 value Wok in
    ⟨ suc zero ,
      ⟨ castOK (appᵐOK Uok (castOK Wok (≤1⇒≤2 W≤1))) z≤n ,
        s≤s z≤n ⟩ ⟩
  preserve-okᵐ μok (ecAppOK (ecAbsOK Mok)) Λ-β
    with subst-ec-meta-ok Mok
  ... | ⟨ k , ⟨ Mok′ , k≤n ⟩ ⟩ =
    ⟨ k , ⟨ Mok′ , ≤-trans k≤n (delayed-ok≤2 Mok) ⟩ ⟩
  preserve-okᵐ μok (ecAppOK (castOK Uok n≤2)) (Λ-β-cast raw) =
    ⟨ suc zero , ⟨ castOK (ecAppOK Uok) z≤n , s≤s z≤n ⟩ ⟩
  preserve-okᵐ μok (subElimOK (subIntroOK Mok)) sub-β =
    ⟨ _ , ⟨ weaken-okᵐ Mok , delayed-ok≤2 Mok ⟩ ⟩
  preserve-okᵐ μok (subElimOK (castOK Uok n≤2)) (sub-β-cast raw) =
    ⟨ suc zero , ⟨ castOK (subElimOK Uok) z≤n , s≤s z≤n ⟩ ⟩
  preserve-okᵐ μok (subElimDynOK (castOK Uok n≤2)) (sub-cast-success raw e₁<:e₂) =
    ⟨ zero , ⟨ subElimOK (castOK Uok n≤2) , z≤n ⟩ ⟩
  preserve-okᵐ μok C₁ok (sub-cast-sub-fail raw ¬e₁<:e₂) =
    ⟨ zero , ⟨ blameOK , z≤n ⟩ ⟩
  preserve-okᵐ μok C₁ok (sub-cast-fail raw ground ¬G⦊e₁<:e₂) =
    ⟨ zero , ⟨ blameOK , z≤n ⟩ ⟩
  preserve-okᵐ μok (refOK Vok) (ref value) =
    ⟨ zero , ⟨ addrOK , z≤n ⟩ ⟩
  preserve-okᵐ μok (derefOK addrOK) (deref lookup)
    with heap-values-ok-lookup μok lookup
  ... | ⟨ value , ⟨ m , Vok ⟩ ⟩ =
    ⟨ m , ⟨ Vok , ≤-trans (value-ok≤1 value Vok) (s≤s z≤n) ⟩ ⟩
  preserve-okᵐ μok (assignOK addrOK Vok) (assign value μ↦μ′) =
    ⟨ zero , ⟨ constᵐOK , z≤n ⟩ ⟩
  preserve-okᵐ μok (assignOK (castOK addrOK addr≤2) Vok) (assign-cast value) =
    let V≤1 = value-ok≤1 value Vok in
    ⟨ zero , ⟨ assignOK addrOK (castOK Vok (≤1⇒≤2 V≤1)) , z≤n ⟩ ⟩
  preserve-okᵐ μok (derefOK (castOK addrOK addr≤2)) deref-cast =
    ⟨ suc zero , ⟨ castOK (derefOK addrOK) z≤n , s≤s z≤n ⟩ ⟩
  preserve-okᵐ μok (castOK (castOK {n = n} Uok n≤2) m≤2) (cast-compose raw) =
    ⟨ suc n , ⟨ castOK Uok n≤2 , ≤2+suc (suc n) ⟩ ⟩
  preserve-okᵐ μok (castOK {n = n} Uok n≤2) (cast-id⋆ raw) =
    ⟨ n , ⟨ Uok , ≤2+suc n ⟩ ⟩
  preserve-okᵐ μok (castOK {n = n} Uok n≤2) (cast-idι raw) =
    ⟨ n , ⟨ Uok , ≤2+suc n ⟩ ⟩
  preserve-okᵐ μok C₁ok (cast-blame raw) =
    ⟨ zero , ⟨ blameOK , z≤n ⟩ ⟩

multi-preserve-heap-values-okᵒ : ∀ {C₁ C₂ e}
  → ⊢ (C₁ .μ) ok
  → false ⊢ᵒ C₁ .M ok
  → C₁ ∣ e —↠ᵒ C₂
    --------------------------
  → ⊢ (C₂ .μ) ok
multi-preserve-heap-values-okᵒ μok Cok (C ∣ e ∎ᵒ) = μok
multi-preserve-heap-values-okᵒ
  μok Cok
  (_∣_—→ᵒ⟨_⟩_ C₁ e {C₂ = C₂} {C₃ = C₃} C₁—→C₂ C₂—↠C₃) =
  multi-preserve-heap-values-okᵒ
    (preserve-heap-values-okᵒ μok Cok C₁—→C₂)
    (preserve-okᵒ μok Cok C₁—→C₂)
    C₂—↠C₃

multi-preserve-heap-values-okᵐ : ∀ {ctx C₁ C₂ n}
  → ⊢ (C₁ .μ) ok
  → n ∣ false ⊢ᵐ C₁ .M ok
  → ctx / C₁ —↠ᵐ C₂
    --------------------------
  → ⊢ (C₂ .μ) ok
multi-preserve-heap-values-okᵐ μok Cok (C ∎ᵐ) = μok
multi-preserve-heap-values-okᵐ
  μok Cok
  (_/_—→ᵐ⟨_⟩_ ctx C₁ {C₂ = C₂} {C₃ = C₃} C₁—→C₂ C₂—↠C₃)
  with preserve-okᵐ μok Cok C₁—→C₂
... | ⟨ m , ⟨ C₂ok , m≤2+n ⟩ ⟩ =
  multi-preserve-heap-values-okᵐ
    (preserve-heap-values-okᵐ μok Cok C₁—→C₂)
    C₂ok
    C₂—↠C₃

multi-preserve-okᵒ : ∀ {C₁ C₂ e}
  → ⊢ (C₁ .μ) ok
  → false ⊢ᵒ C₁ .M ok
  → C₁ ∣ e —↠ᵒ C₂
    -----------------------
  → false ⊢ᵒ C₂ .M ok
multi-preserve-okᵒ μok Cok (C ∣ e ∎ᵒ) = Cok
multi-preserve-okᵒ
  μok Cok
  (_∣_—→ᵒ⟨_⟩_ C₁ e {C₂ = C₂} {C₃ = C₃} C₁—→C₂ C₂—↠C₃) =
  multi-preserve-okᵒ
    (preserve-heap-values-okᵒ μok Cok C₁—→C₂)
    (preserve-okᵒ μok Cok C₁—→C₂)
    C₂—↠C₃

multi-preserve-okᵐ : ∀ {ctx C₁ C₂ n}
  → ⊢ (C₁ .μ) ok
  → n ∣ false ⊢ᵐ C₁ .M ok
  → ctx / C₁ —↠ᵐ C₂
    -----------------------------------
  → Σ[ m ∈ ℕ ] m ∣ false ⊢ᵐ C₂ .M ok
multi-preserve-okᵐ μok Cok (C ∎ᵐ) =
  ⟨ _ , Cok ⟩
multi-preserve-okᵐ
  μok Cok
  (_/_—→ᵐ⟨_⟩_ ctx C₁ {C₂ = C₂} {C₃ = C₃} C₁—→C₂ C₂—↠C₃)
  with preserve-okᵐ μok Cok C₁—→C₂
... | ⟨ m , ⟨ C₂ok , m≤2+n ⟩ ⟩ =
  multi-preserve-okᵐ
    (preserve-heap-values-okᵐ μok Cok C₁—→C₂)
    C₂ok
    C₂—↠C₃
