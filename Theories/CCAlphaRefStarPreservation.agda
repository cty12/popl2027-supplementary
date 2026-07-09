{-# OPTIONS --rewriting #-}

module Theories.CCAlphaRefStarPreservation where

open import Data.List using ([]; _∷_; _∷ʳ_; [_]; _++_)
open import Data.List.Relation.Unary.All using ([]) renaming (_∷_ to _∷ᴬ_)
open import Data.List.Relation.Unary.All.Properties using (∷ʳ⁺)
open import Data.Nat.Properties using (≤-trans; <-≤-trans)
open import Data.Product using (Σ-syntax; ∃-syntax; _×_) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit using (tt)

open import Theories.Utils
open import Theories.CCAlphaRefStarSyntaxAndTypeSystem
open import Theories.CCAlphaRefStarSemantics
open import Theories.Values
open import Theories.CodeCtxWeakening
  using (code-octx-≼; meta-octx-≼)
open import Theories.ECCtxWeakening
open import Theories.Heap
open import Theories.HeapCtxWeakening
  using (code-heapctx-≼; meta-heapctx-≼)
open import Theories.CodeSubstLemmas
open import Theories.MetaSubstLemmas
open import Theories.ECSubstLemmas using (subst-ec-meta; subst-ec-coercion)
open import Theories.SubCtxWeakening
  using
    (subctx-refl; subctx-global-weaken; global-subedge-last; code-⊆ˢ; meta-⊆ˢ;
     meta-coercion-⊆ˢ)
open import Theories.SubCtxDrop using (subtype-drop-coercion; subtype-drop-term)
open import Theories.WellTypedTermImpliesWellFormedTypes using (wt-impl-wf-mtype)
import Theories.CoercionSequences.EC.Definition as EC
import Theories.CoercionSequences.Code.Definition as OC
import Theories.CoercionSequences.Meta.Definition as MC
import Theories.CoercionSequences.Meta.Preservation as MCP


-- | Helpers for cases where only the term changes in the configuration
-- | but not anything else.
mkCodePreservation : ∀ {Δ Θ Γᵒ μ Mᵒ Nᵒ Σ e T}
  → Δ ⊢ᵉ e
  → (⊢C₁ : WTCodeConfig (config Δ Θ Γᵒ μ Mᵒ) Σ e T)
  → Δ ; ⟨ Θ , Γᵒ , ∅ , Σ ⟩ ; e ⊢ᵒ Nᵒ ⦂ T
    ---------------------------------------------------------------------
  → ∃[ Σ₂ ] Σ[ ⊢C₂ ∈ WTCodeConfig (config Δ Θ Γᵒ μ Nᵒ) Σ₂ e T ]
      config Δ Θ Γᵒ μ Mᵒ ⊆ꟲ config Δ Θ Γᵒ μ Nᵒ × (Σ ≼ Σ₂) × (Δ ⊢ᵉ e)
mkCodePreservation {Σ = Σ} ⊢e ⊢C ⊢Nᵒ =
  ⟨ Σ ,
    wtCodeConfig (⊢C .⊢Θ) (⊢C .⊢Γᵒ) (⊢C .⊢Σ) (⊢C .⊢μ) ⊢Nᵒ ,
    config⊆ ⊆ᵉ-refl ≼ᵒ-refl subctx-refl , ≼-refl , ⊢e ⟩

mkMetaPreservation : ∀ {Δ Θ Γᵒ μ₁ μ₂ M N Σ A}
  → (⊢C₁ : WTMetaConfig (config Δ Θ Γᵒ μ₁ M) Σ A)
  → Δ ; Θ ; Γᵒ ; Σ ⊢ᴴ μ₂
  → Δ ; ⟨ Θ , Γᵒ , ∅ , Σ ⟩ ⊢ᵐ N ⦂ A
    ---------------------------------------------------------------
  → ∃[ Σ₂ ] Σ[ ⊢C₂ ∈ WTMetaConfig (config Δ Θ Γᵒ μ₂ N) Σ₂ A ]
      config Δ Θ Γᵒ μ₁ M ⊆ꟲ config Δ Θ Γᵒ μ₂ N × (Σ ≼ Σ₂)
mkMetaPreservation {Σ = Σ} ⊢C ⊢μ₂ ⊢N =
  ⟨ Σ ,
    wtMetaConfig (⊢C .⊢Θ) (⊢C .⊢Γᵒ) (⊢C .⊢Σ) ⊢μ₂ ⊢N ,
    config⊆ ⊆ᵉ-refl ≼ᵒ-refl subctx-refl , ≼-refl ⟩

++ᵐ-preserve : ∀ {Δ Θ c̅ d̅ A B C}
  → Δ MC.; Θ ⊢ᵐ̅ c̅ ⦂ A ⇒ B
  → Δ MC.; Θ ⊢ᵐ̅ d̅ ⦂ B ⇒ C
    ----------------------------------
  → Δ MC.; Θ ⊢ᵐ̅ c̅ ++ d̅ ⦂ A ⇒ C
++ᵐ-preserve (MC.⊢[] _) ⊢d̅ = ⊢d̅
++ᵐ-preserve (MC.⊢; ⊢c ⊢c̅) ⊢d̅ =
  MC.⊢; ⊢c (++ᵐ-preserve ⊢c̅ ⊢d̅)

sub-inj-prefix : ∀ {Δ Θ c̅ A e₁ e₂}
  → Δ MC.; Θ ⊢ᵐ̅ c̅ ++ [ ((e₁ <: e₂ => ⋆) MC.！) gsub ] ⦂ A ⇒ ⋆
    -------------------------------------------------------------------
  → Δ MC.; Θ ⊢ᵐ̅ c̅ ⦂ A ⇒ e₁ <: e₂ => ⋆
sub-inj-prefix {c̅ = []} (MC.⊢; (MC.⊢! ⊢G gsub) (MC.⊢[] _)) =
  MC.⊢[] ⊢G
sub-inj-prefix {c̅ = c ∷ c̅} (MC.⊢; ⊢c ⊢c̅++inj) =
  MC.⊢; ⊢c (sub-inj-prefix {c̅ = c̅} ⊢c̅++inj)


-- | Packaged-up weakening lemmas for proving preservation of congruence
code-weaken : ∀ {Δ₁ Δ₂ Θ₁ Θ₂ Γᵒ₁ Γᵒ₂ Γᵐ Σ₁ Σ₂ e M T}
  → Δ₁ ⊆ᵉ Δ₂
  → Γᵒ₁ ≼ᵒ Γᵒ₂
  → Θ₁ ⊆ˢ Θ₂
  → Σ₁ ≼ Σ₂
  → Δ₁ ; ⟨ Θ₁ , Γᵒ₁ , Γᵐ , Σ₁ ⟩ ; e ⊢ᵒ M ⦂ T
    ------------------------------------------------
  → Δ₂ ; ⟨ Θ₂ , Γᵒ₂ , Γᵐ , Σ₂ ⟩ ; e ⊢ᵒ M ⦂ T
code-weaken Δ₁⊆Δ₂ Γᵒ₁≼Γᵒ₂ Θ₁⊆Θ₂ Σ₁≼Σ₂ ⊢M =
  code-heapctx-≼ Σ₁≼Σ₂ (code-octx-≼ Γᵒ₁≼Γᵒ₂ (code-⊆ˢ Θ₁⊆Θ₂ (code-ecctx-weaken Δ₁⊆Δ₂ ⊢M)))

meta-weaken : ∀ {Δ₁ Δ₂ Θ₁ Θ₂ Γᵒ₁ Γᵒ₂ Γᵐ Σ₁ Σ₂ M A}
  → Δ₁ ⊆ᵉ Δ₂
  → Γᵒ₁ ≼ᵒ Γᵒ₂
  → Θ₁ ⊆ˢ Θ₂
  → Σ₁ ≼ Σ₂
  → Δ₁ ; ⟨ Θ₁ , Γᵒ₁ , Γᵐ , Σ₁ ⟩ ⊢ᵐ M ⦂ A
    ------------------------------------------
  → Δ₂ ; ⟨ Θ₂ , Γᵒ₂ , Γᵐ , Σ₂ ⟩ ⊢ᵐ M ⦂ A
meta-weaken Δ₁⊆Δ₂ Γᵒ₁≼Γᵒ₂ Θ₁⊆Θ₂ Σ₁≼Σ₂ ⊢M =
  meta-heapctx-≼ Σ₁≼Σ₂ (meta-octx-≼ Γᵒ₁≼Γᵒ₂ (meta-⊆ˢ Θ₁⊆Θ₂ (meta-ecctx-weaken Δ₁⊆Δ₂ ⊢M)))


-- | Plug inversion lemmas for code and meta congruence rules
code-plug-inversion : ∀ {Δ Θ Γᵒ Γᵐ Σ e Fᵒ Mᵒ T}
  → Δ ; ⟨ Θ , Γᵒ , Γᵐ , Σ ⟩ ; e ⊢ᵒ plugᵒ Fᵒ Mᵒ ⦂ T
    ------------------------------------------------------
  → Σ[ S ∈ OType ]
      (Δ ; ⟨ Θ , Γᵒ , Γᵐ , Σ ⟩ ; e ⊢ᵒ Mᵒ ⦂ S)
    × ∀ {Δ′ Θ′ Γᵒ′ Σ′ Nᵒ}
        → Δ ⊆ᵉ Δ′
        → Γᵒ ≼ᵒ Γᵒ′
        → Θ ⊆ˢ Θ′
        → Σ ≼ Σ′
        → Δ′ ; ⟨ Θ′ , Γᵒ′ , Γᵐ , Σ′ ⟩ ; e ⊢ᵒ Nᵒ ⦂ S
        → Δ′ ; ⟨ Θ′ , Γᵒ′ , Γᵐ , Σ′ ⟩ ; e ⊢ᵒ plugᵒ Fᵒ Nᵒ ⦂ T
code-plug-inversion {Fᵒ = □· Mᵒ₂} (⊢appᵒ {T₁ = T₁} {T₂ = T₂} ⊢Mᵒ ⊢Mᵒ₂) =
  ⟨ T₁ ⇒ T₂ , ⊢Mᵒ , (λ Δ⊆ Γᵒ≼ Θ⊆ Σ≼ ⊢Nᵒ → ⊢appᵒ ⊢Nᵒ (code-weaken Δ⊆ Γᵒ≼ Θ⊆ Σ≼ ⊢Mᵒ₂)) ⟩
code-plug-inversion {Fᵒ = (Lᵒ ·□) vᵒ} (⊢appᵒ {T₁ = T₁} ⊢Lᵒ ⊢Mᵒ) =
  ⟨ T₁ , ⊢Mᵒ , (λ Δ⊆ Γᵒ≼ Θ⊆ Σ≼ ⊢Nᵒ → ⊢appᵒ (code-weaken Δ⊆ Γᵒ≼ Θ⊆ Σ≼ ⊢Lᵒ) ⊢Nᵒ) ⟩


meta-plug-inversion : ∀ {Δ Θ Γᵒ Γᵐ Σ F M A}
  → Δ ; ⟨ Θ , Γᵒ , Γᵐ , Σ ⟩ ⊢ᵐ plugᵐ F M ⦂ A
    ------------------------------------------------------
  → Σ[ B ∈ MType ]
      (Δ ; ⟨ Θ , Γᵒ , Γᵐ , Σ ⟩ ⊢ᵐ M ⦂ B)
    × ∀ {Δ′ Θ′ Γᵒ′ Σ′ N}
        → Δ ⊆ᵉ Δ′
        → Γᵒ ≼ᵒ Γᵒ′
        → Θ ⊆ˢ Θ′
        → Σ ≼ Σ′
        → Δ′ ; ⟨ Θ′ , Γᵒ′ , Γᵐ , Σ′ ⟩ ⊢ᵐ N ⦂ B
        → Δ′ ; ⟨ Θ′ , Γᵒ′ , Γᵐ , Σ′ ⟩ ⊢ᵐ plugᵐ F N ⦂ A
meta-plug-inversion {F = □· M₂} (⊢appᵐ {A = A} {B = B} ⊢M ⊢M₂) =
  ⟨ A ⇒ B , ⊢M ,
    (λ Δ⊆ Γᵒ≼ Θ⊆ Σ≼ ⊢N → ⊢appᵐ ⊢N (meta-weaken Δ⊆ Γᵒ≼ Θ⊆ Σ≼ ⊢M₂)) ⟩
meta-plug-inversion {F = (L ·□) v} (⊢appᵐ {A = A} ⊢L ⊢M) =
  ⟨ A , ⊢M ,
    (λ Δ⊆ Γᵒ≼ Θ⊆ Σ≼ ⊢N → ⊢appᵐ (meta-weaken Δ⊆ Γᵒ≼ Θ⊆ Σ≼ ⊢L) ⊢N) ⟩
meta-plug-inversion {F = ref□} (⊢ref {A = A} ⊢M) =
  ⟨ A , ⊢M , (λ Δ⊆ Γᵒ≼ Θ⊆ Σ≼ ⊢N → ⊢ref ⊢N) ⟩
meta-plug-inversion {F = □:= M₂} (⊢assign {A = A} ⊢M ⊢M₂) =
  ⟨ Ref A , ⟨ ⊢M , (λ Δ⊆ Γᵒ≼ Θ⊆ Σ≼ ⊢N → ⊢assign ⊢N (meta-weaken Δ⊆ Γᵒ≼ Θ⊆ Σ≼ ⊢M₂)) ⟩ ⟩
meta-plug-inversion {F = (V :=□) v} (⊢assign {A = A} ⊢V ⊢M) =
  ⟨ A , ⊢M ,
    (λ Δ⊆ Γᵒ≼ Θ⊆ Σ≼ ⊢N → ⊢assign (meta-weaken Δ⊆ Γᵒ≼ Θ⊆ Σ≼ ⊢V) ⊢N) ⟩
meta-plug-inversion {F = !□} (⊢deref {A = A} ⊢M) =
  ⟨ Ref A , ⟨ ⊢M , (λ Δ⊆ Γᵒ≼ Θ⊆ Σ≼ ⊢N → ⊢deref ⊢N) ⟩ ⟩
meta-plug-inversion {F = □·[ e ]} (⊢ecapp {A = A} ⊢M ⊢e) =
  ⟨ ∀̇ A , ⊢M ,
    (λ Δ⊆ Γᵒ≼ Θ⊆ Σ≼ ⊢N → ⊢ecapp ⊢N (ec-weaken Δ⊆ ⊢e)) ⟩
meta-plug-inversion {F = □●} (⊢subelim {A = A} {e₁ = e₁} {e₂ = e₂} ⊢M e₁<:e₂) =
  ⟨ e₁ <: e₂ => A , ⊢M ,
    (λ Δ⊆ Γᵒ≼ Θ⊆ Σ≼ ⊢N → ⊢subelim ⊢N (Θ⊆ .subtype⊆ e₁<:e₂)) ⟩
meta-plug-inversion {F = □★ ℓ} (⊢subelim⋆ ⊢M .ℓ) =
  ⟨ ⋆ , ⊢M , (λ Δ⊆ Γᵒ≼ Θ⊆ Σ≼ ⊢N → ⊢subelim⋆ ⊢N ℓ) ⟩
meta-plug-inversion {F = □⟨ c ⟩} (⊢cast {A = A} {B = B} ⊢M ⊢c) =
  ⟨ A , ⊢M ,
    (λ Δ⊆ Γᵒ≼ Θ⊆ Σ≼ ⊢N →
      ⊢cast ⊢N (meta-coercion-⊆ˢ Θ⊆ (meta-coercion-ecctx-weaken Δ⊆ ⊢c))) ⟩


mutual
  preserveᵒ : ∀ {C₁ C₂ Σ₁ e T} {⊢e : C₁ .Δ ⊢ᵉ e}
    → (⊢C₁ : WTCodeConfig C₁ Σ₁ e T)
    → C₁ ∣ e —→ᵒ C₂
      ------------------------------------------------
    → ∃[ Σ₂ ] Σ[ ⊢C₂ ∈ WTCodeConfig C₂ Σ₂ e T ]
        C₁ ⊆ꟲ C₂ × (Σ₁ ≼ Σ₂) × (C₂ .Δ ⊢ᵉ e)
  preserveᵒ {⊢e = ⊢e} ⊢C (ξ-code Fᵒ Mᵒ—→Nᵒ)
    with code-plug-inversion (⊢C .⊢M)
  ... | ⟨ T₀ , ⊢Mᵒ , plug-wt ⟩ =
    let ⊢Mᵒ₁ = wtCodeConfig (⊢C .⊢Θ) (⊢C .⊢Γᵒ) (⊢C .⊢Σ) (⊢C .⊢μ) ⊢Mᵒ
        ⟨ Σ₂ , wtCodeConfig ⊢Θ₂ ⊢Γᵒ₂ ⊢Σ₂ ⊢μ₂ ⊢Nᵒ , C₁⊆C₂ , Σ₁≼Σ₂ , Δ₂⊢e ⟩ =
          preserveᵒ {⊢e = ⊢e} ⊢Mᵒ₁ Mᵒ—→Nᵒ in
    ⟨ Σ₂ ,
      wtCodeConfig ⊢Θ₂ ⊢Γᵒ₂ ⊢Σ₂ ⊢μ₂ (plug-wt (C₁⊆C₂ .Δ⊆) (C₁⊆C₂ .Γᵒ≼) (C₁⊆C₂ .Θ⊆) Σ₁≼Σ₂ ⊢Nᵒ) ,
      config⊆ (C₁⊆C₂ .Δ⊆) (C₁⊆C₂ .Γᵒ≼) (C₁⊆C₂ .Θ⊆) , Σ₁≼Σ₂ , Δ₂⊢e ⟩
  preserveᵒ {⊢e = ⊢e} ⊢C (ξ-code-blame {ℓ = ℓ} Fᵒ) = mkCodePreservation ⊢e ⊢C (⊢blameᵒ ℓ)
  preserveᵒ {⊢e = ⊢e} (wtCodeConfig ⊢Θ ⊢Γᵒ ⊢Σ ⊢μ (⊢splice ⊢M O=T)) (ξ-splice M—→N) =
    let ⊢M₁ = wtMetaConfig ⊢Θ ⊢Γᵒ ⊢Σ ⊢μ ⊢M
        ⟨ Σ₂ , wtMetaConfig ⊢Θ₂ ⊢Γᵒ₂ ⊢Σ₂ ⊢μ₂ ⊢N , C₁⊆C₂ , Σ₁≼Σ₂ ⟩ =
          preserveᵐ ⊢M₁ M—→N
        Δ₂⊢e = ec-weaken (C₁⊆C₂ .Δ⊆) ⊢e in
    ⟨ Σ₂ ,
      wtCodeConfig ⊢Θ₂ ⊢Γᵒ₂ ⊢Σ₂ ⊢μ₂ (⊢splice ⊢N O=T) ,
      config⊆ (C₁⊆C₂ .Δ⊆) (C₁⊆C₂ .Γᵒ≼) (C₁⊆C₂ .Θ⊆) , Σ₁≼Σ₂ , Δ₂⊢e ⟩
  preserveᵒ {⊢e = ⊢e} ⊢C (splice-blame {ℓ = ℓ}) =
    mkCodePreservation ⊢e ⊢C (⊢blameᵒ ℓ)
  preserveᵒ {⊢e = ⊢e} ⊢C (splice-β vᵒ) =
    mkCodePreservation ⊢e ⊢C (splice-beta-inv (⊢C .⊢M))
    where  -- inversion on typing derivation
    splice-beta-inv : ∀ {Δ Θ Γᵒ Σ e₁ e Vᵒ T}
      → Δ ; ⟨ Θ , Γᵒ , ∅ , Σ ⟩ ; e ⊢ᵒ ~ (‶ Vᵒ ″ e₁) ⦂ T
      → Δ ; ⟨ Θ , Γᵒ , ∅ , Σ ⟩ ; e ⊢ᵒ Vᵒ ⦂ T
    splice-beta-inv (⊢splice (⊢quote ⊢V _ O↪T₁) O↪T₂) rewrite ↪ᵒ-unique O↪T₁ O↪T₂ = ⊢V
  preserveᵒ {⊢e = ⊢e} ⊢C (splice-sub vᵒ) =
    mkCodePreservation ⊢e ⊢C (splice-sub-inv vᵒ (⊢C .⊢M))
    where -- inversion on the typing derivation
    splice-sub-inv : ∀ {Δ Θ Γᵒ Σ e₁ e₂ e Vᵒ T}
      → CodeValue Vᵒ
      → Δ ; ⟨ Θ , Γᵒ , ∅ , Σ ⟩ ; e ⊢ᵒ ~ ((‶ Vᵒ ″ e₁) ⟨ [ MC.‶ [] ″ [ EC.ec e₁ EC.↑ EC.ec e₂ ] ] ⟩) ⦂ T
      → Δ ; ⟨ Θ , Γᵒ , ∅ , Σ ⟩ ; e ⊢ᵒ Vᵒ ⦂ T
    splice-sub-inv stlc (⊢splice (⊢cast (⊢quote ⊢V ⊢e₁ O↪T₁)
                         (MC.⊢; (MC.⊢code OC.⊢[]
                                                   (EC.⊢; (EC.⊢↑ _ _ (<:-ec e₁<:e₂)) (EC.⊢[] _)))
                                (MC.⊢[] _))) O↪T₂)
      rewrite ↪ᵒ-unique O↪T₁ O↪T₂ = codevalue-weaken-ec ⊢V stlc e₁<:e₂
  preserveᵒ {C₁ = config Δ Θ Γᵒ μ (ƛ T₀ ˙ Nᵒ)}
             {Σ₁ = Σ} {e = e} {⊢e = ⊢e}
             (wtCodeConfig ⊢Θ ⊢Γᵒ ⊢Σ ⊢μ (⊢lamᵒ ⊢Nᵒ)) code-λ =
    ⟨ Σ ,
      wtCodeConfig
        (subctx-wf-global-ext {Θ = Θ} ⊢Θ ⊢e)
        (octx-wf-global-ext {Δ = Δ} {Γᵒ = Γᵒ} {T = T₀} ⊢Γᵒ)
        (mctx-weaken ⊆ᵉ-snoc ⊢Σ) (heap-code-alloc ⊢μ)
        (⊢lamᵒ-val (globalEC (s≤s ≤-refl) (Δ .cutoff≤size))
          (drop-snoc-last (Γᵒ .cutoff) (Γᵒ .entries) {x = ⟨ T₀ , freshᵉ Δ ⟩}
            (Γᵒ .cutoff≤length))
          (global-subedge-last Θ) <:-refl
          (subst-code-λ-body ⊢Γᵒ ⊢Nᵒ)) ,
      config⊆ ⊆ᵉ-snoc ≼ᵒ-snoc subctx-global-weaken , ≼-refl , ec-weaken ⊆ᵉ-snoc ⊢e ⟩
  preserveᵒ {⊢e = ⊢e} ⊢C (ξ-code-λ̅-blame {ℓ = ℓ}) =
    mkCodePreservation ⊢e ⊢C (⊢blameᵒ ℓ)
  preserveᵒ {C₁ = config Δ Θ Γᵒ μ (ƛ̅ ε ˙ Mᵒ)} {Σ₁ = Σ} {⊢e = ⊢e}
            (wtCodeConfig ⊢Θ ⊢Γᵒ ⊢Σ ⊢μ ())
            (ξ-code-λ̅ Mᵒ—→Nᵒ)
  preserveᵒ {C₁ = config Δ Θ Γᵒ μ (ƛ̅ ` α ˙ Mᵒ)}
             {T = ` ι} {⊢e = ⊢e}
             (wtCodeConfig ⊢Θ ⊢Γᵒ ⊢Σ ⊢μ ())
             (ξ-code-λ̅ Mᵒ—→Nᵒ)
  preserveᵒ {C₁ = config Δ Θ Γᵒ μ (ƛ̅ ` α ˙ Mᵒ)} {Σ₁ = Σ} {T = T₁ ⇒ T₂} {⊢e = ⊢e}
            (wtCodeConfig ⊢Θ ⊢Γᵒ ⊢Σ ⊢μ (⊢lamᵒ-val (globalEC α<Δ cutoff≤α) owner edge e′<:e ⊢Mᵒ))
            (ξ-code-λ̅ Mᵒ—→Nᵒ) =
    let ⊢Mᵒ₁ = wtCodeConfig ⊢Θ ⊢Γᵒ ⊢Σ ⊢μ ⊢Mᵒ
        ⟨ Σ₂ , wtCodeConfig ⊢Θ₂ ⊢Γᵒ₂ ⊢Σ₂ ⊢μ₂ ⊢Nᵒ , C₁⊆C₂ , Σ₁≼Σ₂ , _ ⟩ =
            preserveᵒ {⊢e = wf-` α<Δ} ⊢Mᵒ₁ Mᵒ—→Nᵒ
        Δ₂⊢e = ec-weaken (C₁⊆C₂ .Δ⊆) ⊢e in
    ⟨ Σ₂ ,
      wtCodeConfig ⊢Θ₂ ⊢Γᵒ₂ ⊢Σ₂ ⊢μ₂
        (⊢lamᵒ-val (globalEC (<-≤-trans α<Δ (C₁⊆C₂ .Δ⊆ .size≤)) (≤-trans (C₁⊆C₂ .Δ⊆ .cutoff≤) cutoff≤α))
          (C₁⊆C₂ .Γᵒ≼ .globalEntries⊆ owner)
          ((C₁⊆C₂ .Θ⊆) .globalEdge⊆ edge)
          ((C₁⊆C₂ .Θ⊆) .subtype⊆ e′<:e)
          ⊢Nᵒ) ,
        config⊆ (C₁⊆C₂ .Δ⊆) (C₁⊆C₂ .Γᵒ≼) (C₁⊆C₂ .Θ⊆) , Σ₁≼Σ₂ , Δ₂⊢e ⟩

  preserveᵐ : ∀ {C₁ C₂ Σ₁ A}
    → (⊢C₁ : WTMetaConfig C₁ Σ₁ A)
    → C₁ —→ᵐ C₂
      ---------------------------------------------------------------
    → ∃[ Σ₂ ] Σ[ ⊢C₂ ∈ WTMetaConfig C₂ Σ₂ A ] C₁ ⊆ꟲ C₂ × (Σ₁ ≼ Σ₂)
  preserveᵐ ⊢C (ξ-meta F M—→N)
    with meta-plug-inversion (⊢C .⊢M)
  ... | ⟨ B , ⊢M , plug-wt ⟩ =
    let ⊢M₁ = wtMetaConfig (⊢C .⊢Θ) (⊢C .⊢Γᵒ) (⊢C .⊢Σ) (⊢C .⊢μ) ⊢M
        ⟨ Σ₂ , wtMetaConfig ⊢Θ₂ ⊢Γᵒ₂ ⊢Σ₂ ⊢μ₂ ⊢N , C₁⊆C₂ , Σ₁≼Σ₂ ⟩ =
          preserveᵐ ⊢M₁ M—→N in
    ⟨ Σ₂ ,
      wtMetaConfig ⊢Θ₂ ⊢Γᵒ₂ ⊢Σ₂ ⊢μ₂
        (plug-wt (C₁⊆C₂ .Δ⊆) (C₁⊆C₂ .Γᵒ≼) (C₁⊆C₂ .Θ⊆) Σ₁≼Σ₂ ⊢N) ,
        config⊆ (C₁⊆C₂ .Δ⊆) (C₁⊆C₂ .Γᵒ≼) (C₁⊆C₂ .Θ⊆) , Σ₁≼Σ₂ ⟩
  preserveᵐ ⊢C (ξ-meta-blame {ℓ = ℓ} F) =
    mkMetaPreservation ⊢C (⊢C .⊢μ)
      (⊢blame (wt-impl-wf-mtype (wf-ctx (⊢C .⊢Θ) (⊢C .⊢Γᵒ) [] (⊢C .⊢Σ)) (⊢C .⊢M)) ℓ)
  preserveᵐ (wtMetaConfig ⊢Θ ⊢Γᵒ ⊢Σ ⊢μ (⊢quote ⊢Mᵒ ⊢e O=T))
      (ξ-quote Mᵒ—→Nᵒ) =
    let ⊢Mᵒ₁ = wtCodeConfig ⊢Θ ⊢Γᵒ ⊢Σ ⊢μ ⊢Mᵒ
        ⟨ Σ₂ , wtCodeConfig ⊢Θ₂ ⊢Γᵒ₂ ⊢Σ₂ ⊢μ₂ ⊢Nᵒ , C₁⊆C₂ , Σ₁≼Σ₂ , Δ₂⊢e ⟩ =
          preserveᵒ {⊢e = ⊢e} ⊢Mᵒ₁ Mᵒ—→Nᵒ in
    ⟨ Σ₂ ,
      wtMetaConfig ⊢Θ₂ ⊢Γᵒ₂ ⊢Σ₂ ⊢μ₂ (⊢quote ⊢Nᵒ Δ₂⊢e O=T) ,
        config⊆ (C₁⊆C₂ .Δ⊆) (C₁⊆C₂ .Γᵒ≼) (C₁⊆C₂ .Θ⊆) , Σ₁≼Σ₂ ⟩
  preserveᵐ ⊢C@(wtMetaConfig ⊢Θ ⊢Γᵒ ⊢Σ ⊢μ (⊢quote ⊢Mᵒ ⊢e O=T))
      (quote-blame {ℓ = ℓ}) =
    mkMetaPreservation ⊢C ⊢μ (⊢blame (wf-code (wf-ec ⊢e)) ℓ)
  preserveᵐ ⊢C@(wtMetaConfig ⊢Θ ⊢Γᵒ ⊢Σ ⊢μ (⊢appᵐ (⊢lamᵐ ⊢A ⊢N) ⊢V))
      (β v) =
    mkMetaPreservation ⊢C ⊢μ (subst-meta ⊢N ⊢V)
  preserveᵐ ⊢C@(wtMetaConfig ⊢Θ ⊢Γᵒ ⊢Σ ⊢μ (⊢appᵐ (⊢cast ⊢U (MC.⊢; (MC.⊢fun ⊢c ⊢d) (MC.⊢[] _))) ⊢W))
      (β-cast u w inert) =
    mkMetaPreservation ⊢C ⊢μ (⊢cast (⊢appᵐ ⊢U (⊢cast ⊢W ⊢c)) ⊢d)
  preserveᵐ ⊢C@(wtMetaConfig ⊢Θ ⊢Γᵒ ⊢Σ ⊢μ (⊢ecapp (⊢eclam ⊢M) ⊢e))
      Λ-β =
    mkMetaPreservation ⊢C ⊢μ (subst-ec-meta ⊢M ⊢e)
  preserveᵐ ⊢C@(wtMetaConfig ⊢Θ ⊢Γᵒ ⊢Σ ⊢μ (⊢ecapp (⊢cast ⊢U (MC.⊢; (MC.⊢forall ⊢c) (MC.⊢[] _))) ⊢e))
      (Λ-β-cast u) =
    mkMetaPreservation ⊢C ⊢μ (⊢cast (⊢ecapp ⊢U ⊢e) (subst-ec-coercion ⊢c ⊢e))
  preserveᵐ ⊢C@(wtMetaConfig ⊢Θ ⊢Γᵒ ⊢Σ ⊢μ (⊢subelim (⊢subintro ⊢e₁ ⊢e₂ ⊢M) e₁<:e₂))
      sub-β =
    mkMetaPreservation ⊢C ⊢μ (subtype-drop-term ⊢M e₁<:e₂)
  preserveᵐ ⊢C@(wtMetaConfig ⊢Θ ⊢Γᵒ ⊢Σ ⊢μ (⊢subelim (⊢cast ⊢U (MC.⊢; (MC.⊢sub ⊢e₁ ⊢e₂ ⊢c) (MC.⊢[] _))) e₁<:e₂))
      (sub-β-cast u) =
    mkMetaPreservation ⊢C ⊢μ (⊢cast (⊢subelim ⊢U e₁<:e₂) (subtype-drop-coercion ⊢c e₁<:e₂))
  preserveᵐ ⊢C@(wtMetaConfig ⊢Θ ⊢Γᵒ ⊢Σ ⊢μ (⊢subelim⋆ (⊢cast ⊢U ⊢c++inj) ℓ))
      (sub-cast-success u e₁<:e₂ _) =
    mkMetaPreservation ⊢C ⊢μ (⊢subelim (⊢cast ⊢U (sub-inj-prefix ⊢c++inj)) e₁<:e₂)
  preserveᵐ ⊢C@(wtMetaConfig ⊢Θ ⊢Γᵒ ⊢Σ ⊢μ (⊢subelim⋆ ⊢M ℓ))
      (sub-cast-sub-fail u e₁≮:e₂ inert) =
    mkMetaPreservation ⊢C ⊢μ (⊢blame wf-⋆ ℓ)
  preserveᵐ ⊢C@(wtMetaConfig ⊢Θ ⊢Γᵒ ⊢Σ ⊢μ (⊢subelim⋆ ⊢M ℓ))
      (sub-cast-fail u inert G≠sub) =
    mkMetaPreservation ⊢C ⊢μ (⊢blame wf-⋆ ℓ)
  preserveᵐ {Σ₁ = Σ} ⊢C@(wtMetaConfig ⊢Θ ⊢Γᵒ ⊢Σ ⊢μ (⊢ref {A = A} ⊢V))
      (ref v) =
    ⟨ Σ ∷ʳ A ,
      wtMetaConfig ⊢Θ ⊢Γᵒ
        (∷ʳ⁺ ⊢Σ (wt-impl-wf-mtype (wf-ctx ⊢Θ ⊢Γᵒ [] ⊢Σ) ⊢V))
        (heap-extend ⊢μ ⊢V)
        (⊢addr (heap-fresh-lookup ⊢μ)) ,
        config⊆ ⊆ᵉ-refl ≼ᵒ-refl subctx-refl , ≼-snoc ≼-refl ⟩
  preserveᵐ ⊢C@(wtMetaConfig ⊢Θ ⊢Γᵒ ⊢Σ ⊢μ (⊢deref (⊢addr Σ∋A)))
      (deref μ∋V) =
    mkMetaPreservation ⊢C ⊢μ (heap-lookup ⊢μ μ∋V Σ∋A)
  preserveᵐ ⊢C@(wtMetaConfig ⊢Θ ⊢Γᵒ ⊢Σ ⊢μ (⊢assign (⊢addr Σ∋A) ⊢V))
      (assign v μ↦μ′) =
    mkMetaPreservation ⊢C (heap-update ⊢μ μ↦μ′ Σ∋A ⊢V) (⊢constᵐ tt)
  preserveᵐ ⊢C@(wtMetaConfig ⊢Θ ⊢Γᵒ ⊢Σ ⊢μ (⊢assign (⊢cast (⊢addr Σ∋A) (MC.⊢; (MC.⊢ref ⊢c ⊢d) (MC.⊢[] _))) ⊢V))
      (assign-cast v inert) =
    mkMetaPreservation ⊢C ⊢μ (⊢assign (⊢addr Σ∋A) (⊢cast ⊢V ⊢c))
  preserveᵐ ⊢C@(wtMetaConfig ⊢Θ ⊢Γᵒ ⊢Σ ⊢μ (⊢deref (⊢cast (⊢addr Σ∋A) (MC.⊢; (MC.⊢ref ⊢c ⊢d) (MC.⊢[] _)))))
      (deref-cast inert) =
    mkMetaPreservation ⊢C ⊢μ (⊢cast (⊢deref (⊢addr Σ∋A)) ⊢d)
  preserveᵐ ⊢C@(wtMetaConfig ⊢Θ ⊢Γᵒ ⊢Σ ⊢μ (⊢cast ⊢U ⊢c))
      (cast-reduce u c⟼d) =
    mkMetaPreservation ⊢C ⊢μ (⊢cast ⊢U (MCP.preserve c⟼d ⊢c))
  preserveᵐ ⊢C@(wtMetaConfig ⊢Θ ⊢Γᵒ ⊢Σ ⊢μ (⊢cast (⊢cast ⊢U ⊢c) ⊢d))
      (cast-compose u) =
    mkMetaPreservation ⊢C ⊢μ (⊢cast ⊢U (++ᵐ-preserve ⊢c ⊢d))
  preserveᵐ ⊢C@(wtMetaConfig ⊢Θ ⊢Γᵒ ⊢Σ ⊢μ (⊢cast ⊢U (MC.⊢[] _)))
      (cast-id u) =
    mkMetaPreservation ⊢C ⊢μ ⊢U
  preserveᵐ ⊢C@(wtMetaConfig ⊢Θ ⊢Γᵒ ⊢Σ ⊢μ (⊢cast ⊢U (MC.⊢; (MC.⊢⊥ ⊢A ⊢B ℓ) (MC.⊢[] _))))
      (cast-blame u) =
    mkMetaPreservation ⊢C ⊢μ (⊢blame ⊢B ℓ)
