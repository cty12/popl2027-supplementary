module LambdaAlphaRefStar.Theories.SpaceEfficiency.Proofs.HypercoercionCompositionBounded where

open import Data.Nat using (ℕ; _≤_; _⊔_; suc; z≤n; s≤s)
open import Data.Nat.Properties using
  (≤-refl; ≤-trans; m≤m⊔n; m≤n⊔m; ⊔-mono-≤; ⊔-lub)
open import Relation.Nullary using (yes; no)

open import LambdaAlphaRefStar.Theories.EnvClassifiers using
  (SubCtx; ⇑ᵉ-subctx; _,_<:_)

open import LambdaAlphaRefStar.Theories.CodeTypes
open import LambdaAlphaRefStar.Theories.MetaTypes
open import LambdaAlphaRefStar.Theories.SpaceEfficiency.ECHypercoercions
open import LambdaAlphaRefStar.Theories.SpaceEfficiency.ObjectHypercoercions
open import LambdaAlphaRefStar.Theories.SpaceEfficiency.MetaHypercoercions
open import LambdaAlphaRefStar.Theories.SpaceEfficiency.CCAlphaRefStarSizeAndHeight


pos-code-middle-height : (m : OMiddle) → 1 ≤ code-middle-height m
pos-code-middle-height (c₁ ⇒ c₂) = s≤s z≤n
pos-code-middle-height (err ℓ) = ≤-refl
pos-code-middle-height id⋆ = ≤-refl
pos-code-middle-height (idι ι) = ≤-refl


pos-meta-middle-height : (m : MMiddle) → 1 ≤ meta-middle-height m
pos-meta-middle-height (c₁ ⇒ c₂) = s≤s z≤n
pos-meta-middle-height (‶ cᵒ ″ cᵉ) = s≤s z≤n
pos-meta-middle-height (ref c₁ c₂) = s≤s z≤n
pos-meta-middle-height (∀̇ c) = s≤s z≤n
pos-meta-middle-height (e₁ <: e₂ => c) = s≤s z≤n
pos-meta-middle-height (err ℓ) = ≤-refl
pos-meta-middle-height id⋆ = ≤-refl
pos-meta-middle-height (idι ι) = ≤-refl


middle-first≤ : (m₁ m₂ : MMiddle)
  → meta-middle-height m₁ ≤ meta-middle-height m₁ ⊔ meta-middle-height m₂
middle-first≤ m₁ m₂ = m≤m⊔n (meta-middle-height m₁) (meta-middle-height m₂)


left-compose-bound : ∀ a b c d → c ⊔ a ≤ (a ⊔ b) ⊔ (c ⊔ d)
left-compose-bound a b c d =
  ⊔-lub
    (≤-trans (m≤m⊔n c d) (m≤n⊔m (a ⊔ b) (c ⊔ d)))
    (≤-trans (m≤m⊔n a b) (m≤m⊔n (a ⊔ b) (c ⊔ d)))


right-compose-bound : ∀ a b c d → b ⊔ d ≤ (a ⊔ b) ⊔ (c ⊔ d)
right-compose-bound a b c d =
  ⊔-lub
    (≤-trans (m≤n⊔m a b) (m≤m⊔n (a ⊔ b) (c ⊔ d)))
    (≤-trans (m≤n⊔m c d) (m≤n⊔m (a ⊔ b) (c ⊔ d)))


direct-left-compose-bound : ∀ a b c d → a ⊔ c ≤ (a ⊔ b) ⊔ (c ⊔ d)
direct-left-compose-bound a b c d =
  ⊔-lub
    (≤-trans (m≤m⊔n a b) (m≤m⊔n (a ⊔ b) (c ⊔ d)))
    (≤-trans (m≤m⊔n c d) (m≤n⊔m (a ⊔ b) (c ⊔ d)))


binary-compose-bound : ∀ {l r a b c d}
  → l ≤ c ⊔ a
  → r ≤ b ⊔ d
  → suc (l ⊔ r) ≤ suc (a ⊔ b) ⊔ suc (c ⊔ d)
binary-compose-bound {l} {r} {a} {b} {c} {d} l≤ r≤ =
  s≤s
    (⊔-lub
      (≤-trans l≤ (left-compose-bound a b c d))
      (≤-trans r≤ (right-compose-bound a b c d)))


direct-binary-compose-bound : ∀ {l r a b c d}
  → l ≤ a ⊔ c
  → r ≤ b ⊔ d
  → suc (l ⊔ r) ≤ suc (a ⊔ b) ⊔ suc (c ⊔ d)
direct-binary-compose-bound {l} {r} {a} {b} {c} {d} l≤ r≤ =
  s≤s
    (⊔-lub
      (≤-trans l≤ (direct-left-compose-bound a b c d))
      (≤-trans r≤ (right-compose-bound a b c d)))


code-binary-compose-bound : ∀ c₁₁ c₁₂ c₂₁ c₂₂
  → code-hc-height (c₂₁ ⨟ᵒ c₁₁) ≤ code-hc-height c₂₁ ⊔ code-hc-height c₁₁
  → code-hc-height (c₁₂ ⨟ᵒ c₂₂) ≤ code-hc-height c₁₂ ⊔ code-hc-height c₂₂
  → suc (code-hc-height (c₂₁ ⨟ᵒ c₁₁) ⊔ code-hc-height (c₁₂ ⨟ᵒ c₂₂))
      ≤ suc (code-hc-height c₁₁ ⊔ code-hc-height c₁₂) ⊔ suc (code-hc-height c₂₁ ⊔ code-hc-height c₂₂)
code-binary-compose-bound c₁₁ c₁₂ c₂₁ c₂₂ =
  binary-compose-bound
    {a = code-hc-height c₁₁}
    {b = code-hc-height c₁₂}
    {c = code-hc-height c₂₁}
    {d = code-hc-height c₂₂}


meta-binary-compose-bound : ∀ Θ c₁₁ c₁₂ c₂₁ c₂₂
  → meta-hc-height (Θ ⊢ c₂₁ ⨟ᵐ c₁₁) ≤ meta-hc-height c₂₁ ⊔ meta-hc-height c₁₁
  → meta-hc-height (Θ ⊢ c₁₂ ⨟ᵐ c₂₂) ≤ meta-hc-height c₁₂ ⊔ meta-hc-height c₂₂
  → suc (meta-hc-height (Θ ⊢ c₂₁ ⨟ᵐ c₁₁) ⊔ meta-hc-height (Θ ⊢ c₁₂ ⨟ᵐ c₂₂))
      ≤ suc (meta-hc-height c₁₁ ⊔ meta-hc-height c₁₂) ⊔ suc (meta-hc-height c₂₁ ⊔ meta-hc-height c₂₂)
meta-binary-compose-bound Θ c₁₁ c₁₂ c₂₁ c₂₂ =
  binary-compose-bound
    {a = meta-hc-height c₁₁}
    {b = meta-hc-height c₁₂}
    {c = meta-hc-height c₂₁}
    {d = meta-hc-height c₂₂}


code-ec-compose-bound : ∀ Θ c₁ᵒ c₂ᵒ c₁ᵉ c₂ᵉ
  → code-hc-height (c₁ᵒ ⨟ᵒ c₂ᵒ) ≤ code-hc-height c₁ᵒ ⊔ code-hc-height c₂ᵒ
  → suc (code-hc-height (c₁ᵒ ⨟ᵒ c₂ᵒ) ⊔ ec-hc-height (Θ ⊢ c₁ᵉ ⨟ᵉ c₂ᵉ))
      ≤ suc (code-hc-height c₁ᵒ ⊔ ec-hc-height c₁ᵉ) ⊔ suc (code-hc-height c₂ᵒ ⊔ ec-hc-height c₂ᵉ)
code-ec-compose-bound Θ c₁ᵒ c₂ᵒ c₁ᵉ c₂ᵉ =
  λ IH →
    direct-binary-compose-bound
      {a = code-hc-height c₁ᵒ}
      {b = ec-hc-height c₁ᵉ}
      {c = code-hc-height c₂ᵒ}
      {d = ec-hc-height c₂ᵉ}
      IH ≤-refl


mutual

  compose-height-code-middle : (m₁ m₂ : OMiddle)
    → code-middle-height (m₁ ⨟ᵒᵐ m₂) ≤ code-middle-height m₁ ⊔ code-middle-height m₂
  compose-height-code-middle id⋆ m₂ = m≤n⊔m 1 (code-middle-height m₂)
  compose-height-code-middle (idι ι) m₂ = m≤n⊔m 1 (code-middle-height m₂)
  compose-height-code-middle (err ℓ) m₂ = m≤m⊔n 1 (code-middle-height m₂)
  compose-height-code-middle (c₁ ⇒ c₂) (err ℓ) = s≤s z≤n
  compose-height-code-middle (c₁ ⇒ c₂) (c₃ ⇒ c₄)
    with c₃ ⨟ᵒ c₁ | compose-height-code c₃ c₁
       | c₂ ⨟ᵒ c₄ | compose-height-code c₂ c₄
  ... | h₁ ⨾ m₁ ⨾ t₁ | IH₁ | h₂ ⨾ m₂ ⨾ t₂ | IH₂
      with is-error?ᵒ m₁ | is-error?ᵒ m₂
  ...   | yes (error {ℓ}) | _ = s≤s z≤n
  ...   | no _ | yes (error {ℓ}) = s≤s z≤n
  ...   | no _ | no _ =
    binary-compose-bound
      {a = code-hc-height c₁}
      {b = code-hc-height c₂}
      {c = code-hc-height c₃}
      {d = code-hc-height c₄}
      IH₁ IH₂
  compose-height-code-middle (c₁ ⇒ c₂) id⋆ =
    m≤m⊔n (suc (code-hc-height c₁ ⊔ code-hc-height c₂)) 1
  compose-height-code-middle (c₁ ⇒ c₂) (idι ι) =
    m≤m⊔n (suc (code-hc-height c₁ ⊔ code-hc-height c₂)) 1

  compose-height-code : (c₁ c₂ : OHypercoercion)
    → code-hc-height (c₁ ⨟ᵒ c₂) ≤ code-hc-height c₁ ⊔ code-hc-height c₂
  compose-height-code (h₁ ⨾ m₁ ⨾ t₁) (h₂ ⨾ m₂ ⨾ t₂)
    with t₁ ⨟ᵒᵗʰ h₂
  ... | id O = compose-height-code-middle m₁ m₂
  ... | err ℓ
      with is-error?ᵒ m₁
  ...   | yes (error {ℓ′}) = m≤m⊔n 1 (code-middle-height m₂)
  ...   | no _ = ≤-trans (pos-code-middle-height m₁) (m≤m⊔n (code-middle-height m₁) (code-middle-height m₂))
  compose-height-code (h₁ ⨾ m₁ ⨾ t₁) (h₂ ⨾ m₂ ⨾ t₂)
      | G ？ ℓ
      with m₁ | h₁
  ...   | err ℓ′ | _ = m≤m⊔n 1 (code-middle-height m₂)
  ...   | id⋆ | id ⋆ = m≤n⊔m 1 (code-middle-height m₂)
  ...   | id⋆ | G′ ？ ℓ′ = m≤m⊔n 1 (code-middle-height m₂)
  ...   | id⋆ | id (` ι) = m≤m⊔n 1 (code-middle-height m₂)
  ...   | id⋆ | id (O₁ ⇒ O₂) = m≤m⊔n 1 (code-middle-height m₂)
  ...   | idι ι | _ = m≤m⊔n 1 (code-middle-height m₂)
  ...   | c₁ ⇒ c₂ | _ =
    ≤-trans (pos-code-middle-height (c₁ ⇒ c₂))
      (m≤m⊔n (code-middle-height (c₁ ⇒ c₂)) (code-middle-height m₂))
  compose-height-code (h₁ ⨾ m₁ ⨾ t₁) (h₂ ⨾ m₂ ⨾ t₂)
      | G ！
      with m₂ | is-error?ᵒ m₁ | t₂
  ...   | err ℓ | yes (error {ℓ′}) | _ = m≤n⊔m (code-middle-height m₁) 1
  ...   | err ℓ | no _ | _ = m≤n⊔m (code-middle-height m₁) 1
  ...   | id⋆ | _ | id ⋆ = m≤m⊔n (code-middle-height m₁) 1
  ...   | id⋆ | _ | G′ ！ = m≤m⊔n (code-middle-height m₁) 1
  ...   | id⋆ | _ | id (` ι) = m≤m⊔n (code-middle-height m₁) 1
  ...   | id⋆ | _ | id (O₁ ⇒ O₂) = m≤m⊔n (code-middle-height m₁) 1
  ...   | idι ι | _ | _ = m≤m⊔n (code-middle-height m₁) 1
  ...   | c₁ ⇒ c₂ | _ | _ =
    m≤m⊔n (code-middle-height m₁) (code-middle-height (c₁ ⇒ c₂))


mutual

  compose-height-meta-middle : (Θ : SubCtx) (m₁ m₂ : MMiddle)
    → meta-middle-height (Θ ⊢ m₁ ⨟ᵐᵐ m₂) ≤ meta-middle-height m₁ ⊔ meta-middle-height m₂
  compose-height-meta-middle Θ id⋆ m₂ = m≤n⊔m 1 (meta-middle-height m₂)
  compose-height-meta-middle Θ (idι ι) m₂ = m≤n⊔m 1 (meta-middle-height m₂)
  compose-height-meta-middle Θ (err ℓ) m₂ = m≤m⊔n 1 (meta-middle-height m₂)
  compose-height-meta-middle Θ (c₁₁ ⇒ c₁₂) (err ℓ) = s≤s z≤n
  compose-height-meta-middle Θ (c₁₁ ⇒ c₁₂) (c₂₁ ⇒ c₂₂) =
    meta-binary-compose-bound Θ c₁₁ c₁₂ c₂₁ c₂₂
      (compose-height-meta Θ c₂₁ c₁₁)
      (compose-height-meta Θ c₁₂ c₂₂)
  compose-height-meta-middle Θ (c₁₁ ⇒ c₁₂) (‶ cᵒ ″ cᵉ) =
    middle-first≤ (c₁₁ ⇒ c₁₂) (‶ cᵒ ″ cᵉ)
  compose-height-meta-middle Θ (c₁₁ ⇒ c₁₂) (ref c₂₁ c₂₂) =
    middle-first≤ (c₁₁ ⇒ c₁₂) (ref c₂₁ c₂₂)
  compose-height-meta-middle Θ (c₁₁ ⇒ c₁₂) (∀̇ c₂) =
    middle-first≤ (c₁₁ ⇒ c₁₂) (∀̇ c₂)
  compose-height-meta-middle Θ (c₁₁ ⇒ c₁₂) (e₃ <: e₄ => c₂) =
    middle-first≤ (c₁₁ ⇒ c₁₂) (e₃ <: e₄ => c₂)
  compose-height-meta-middle Θ (c₁₁ ⇒ c₁₂) id⋆ =
    middle-first≤ (c₁₁ ⇒ c₁₂) id⋆
  compose-height-meta-middle Θ (c₁₁ ⇒ c₁₂) (idι ι) =
    middle-first≤ (c₁₁ ⇒ c₁₂) (idι ι)
  compose-height-meta-middle Θ (ref c₁₁ c₁₂) (err ℓ) = s≤s z≤n
  compose-height-meta-middle Θ (ref c₁₁ c₁₂) (ref c₂₁ c₂₂) =
    meta-binary-compose-bound Θ c₁₁ c₁₂ c₂₁ c₂₂
      (compose-height-meta Θ c₂₁ c₁₁)
      (compose-height-meta Θ c₁₂ c₂₂)
  compose-height-meta-middle Θ (ref c₁₁ c₁₂) (c₂₁ ⇒ c₂₂) =
    middle-first≤ (ref c₁₁ c₁₂) (c₂₁ ⇒ c₂₂)
  compose-height-meta-middle Θ (ref c₁₁ c₁₂) (‶ cᵒ ″ cᵉ) =
    middle-first≤ (ref c₁₁ c₁₂) (‶ cᵒ ″ cᵉ)
  compose-height-meta-middle Θ (ref c₁₁ c₁₂) (∀̇ c₂) =
    middle-first≤ (ref c₁₁ c₁₂) (∀̇ c₂)
  compose-height-meta-middle Θ (ref c₁₁ c₁₂) (e₃ <: e₄ => c₂) =
    middle-first≤ (ref c₁₁ c₁₂) (e₃ <: e₄ => c₂)
  compose-height-meta-middle Θ (ref c₁₁ c₁₂) id⋆ =
    middle-first≤ (ref c₁₁ c₁₂) id⋆
  compose-height-meta-middle Θ (ref c₁₁ c₁₂) (idι ι) =
    middle-first≤ (ref c₁₁ c₁₂) (idι ι)
  compose-height-meta-middle Θ (∀̇ c₁) (err ℓ) = s≤s z≤n
  compose-height-meta-middle Θ (∀̇ c₁) (∀̇ c₂) =
    s≤s (compose-height-meta (⇑ᵉ-subctx Θ) c₁ c₂)
  compose-height-meta-middle Θ (∀̇ c₁) (c₂₁ ⇒ c₂₂) =
    middle-first≤ (∀̇ c₁) (c₂₁ ⇒ c₂₂)
  compose-height-meta-middle Θ (∀̇ c₁) (‶ cᵒ ″ cᵉ) =
    middle-first≤ (∀̇ c₁) (‶ cᵒ ″ cᵉ)
  compose-height-meta-middle Θ (∀̇ c₁) (ref c₂₁ c₂₂) =
    middle-first≤ (∀̇ c₁) (ref c₂₁ c₂₂)
  compose-height-meta-middle Θ (∀̇ c₁) (e₃ <: e₄ => c₂) =
    middle-first≤ (∀̇ c₁) (e₃ <: e₄ => c₂)
  compose-height-meta-middle Θ (∀̇ c₁) id⋆ =
    middle-first≤ (∀̇ c₁) id⋆
  compose-height-meta-middle Θ (∀̇ c₁) (idι ι) =
    middle-first≤ (∀̇ c₁) (idι ι)
  compose-height-meta-middle Θ (e₁ <: e₂ => c₁) (err ℓ) = s≤s z≤n
  compose-height-meta-middle Θ (e₁ <: e₂ => c₁) (e₃ <: e₄ => c₂) =
    s≤s (compose-height-meta (Θ , e₁ <: e₂) c₁ c₂)
  compose-height-meta-middle Θ (e₁ <: e₂ => c₁) (c₂₁ ⇒ c₂₂) =
    middle-first≤ (e₁ <: e₂ => c₁) (c₂₁ ⇒ c₂₂)
  compose-height-meta-middle Θ (e₁ <: e₂ => c₁) (‶ cᵒ ″ cᵉ) =
    middle-first≤ (e₁ <: e₂ => c₁) (‶ cᵒ ″ cᵉ)
  compose-height-meta-middle Θ (e₁ <: e₂ => c₁) (ref c₂₁ c₂₂) =
    middle-first≤ (e₁ <: e₂ => c₁) (ref c₂₁ c₂₂)
  compose-height-meta-middle Θ (e₁ <: e₂ => c₁) (∀̇ c₂) =
    middle-first≤ (e₁ <: e₂ => c₁) (∀̇ c₂)
  compose-height-meta-middle Θ (e₁ <: e₂ => c₁) id⋆ =
    middle-first≤ (e₁ <: e₂ => c₁) id⋆
  compose-height-meta-middle Θ (e₁ <: e₂ => c₁) (idι ι) =
    middle-first≤ (e₁ <: e₂ => c₁) (idι ι)
  compose-height-meta-middle Θ (‶ c₁ᵒ ″ c₁ᵉ) (err ℓ) = s≤s z≤n
  compose-height-meta-middle Θ (‶ c₁ᵒ ″ c₁ᵉ) (‶ c₂ᵒ ″ c₂ᵉ)
    with c₁ᵒ ⨟ᵒ c₂ᵒ | compose-height-code c₁ᵒ c₂ᵒ
       | Θ ⊢ c₁ᵉ ⨟ᵉ c₂ᵉ
  ... | hᵒ ⨾ mᵒ ⨾ tᵒ | IH | hᵉ ⨾ mᵉ ⨾ tᵉ
      with is-error?ᵒ mᵒ | mᵉ
  ...   | yes (error {ℓ}) | _ = s≤s z≤n
  ...   | no _ | err ℓ = s≤s z≤n
  ...   | no _ | ê₁ ↑ ê₂ =
    direct-binary-compose-bound
      {a = code-hc-height c₁ᵒ}
      {b = ec-hc-height c₁ᵉ}
      {c = code-hc-height c₂ᵒ}
      {d = ec-hc-height c₂ᵉ}
      IH ≤-refl
  compose-height-meta-middle Θ (‶ c₁ᵒ ″ c₁ᵉ) (c₂₁ ⇒ c₂₂) =
    middle-first≤ (‶ c₁ᵒ ″ c₁ᵉ) (c₂₁ ⇒ c₂₂)
  compose-height-meta-middle Θ (‶ c₁ᵒ ″ c₁ᵉ) (ref c₂₁ c₂₂) =
    middle-first≤ (‶ c₁ᵒ ″ c₁ᵉ) (ref c₂₁ c₂₂)
  compose-height-meta-middle Θ (‶ c₁ᵒ ″ c₁ᵉ) (∀̇ c₂) =
    middle-first≤ (‶ c₁ᵒ ″ c₁ᵉ) (∀̇ c₂)
  compose-height-meta-middle Θ (‶ c₁ᵒ ″ c₁ᵉ) (e₃ <: e₄ => c₂) =
    middle-first≤ (‶ c₁ᵒ ″ c₁ᵉ) (e₃ <: e₄ => c₂)
  compose-height-meta-middle Θ (‶ c₁ᵒ ″ c₁ᵉ) id⋆ =
    middle-first≤ (‶ c₁ᵒ ″ c₁ᵉ) id⋆
  compose-height-meta-middle Θ (‶ c₁ᵒ ″ c₁ᵉ) (idι ι) =
    middle-first≤ (‶ c₁ᵒ ″ c₁ᵉ) (idι ι)

  compose-height-meta : (Θ : SubCtx) (c₁ c₂ : MHypercoercion)
    → meta-hc-height (Θ ⊢ c₁ ⨟ᵐ c₂) ≤ meta-hc-height c₁ ⊔ meta-hc-height c₂
  compose-height-meta Θ (h₁ ⨾ m₁ ⨾ t₁) (h₂ ⨾ m₂ ⨾ t₂)
    with t₁ ⨟ᵐᵗʰ h₂
  ... | id A = compose-height-meta-middle Θ m₁ m₂
  ... | err ℓ
      with is-error? m₁
  ...   | yes (error {ℓ′}) = m≤m⊔n 1 (meta-middle-height m₂)
  ...   | no _ = ≤-trans (pos-meta-middle-height m₁) (m≤m⊔n (meta-middle-height m₁) (meta-middle-height m₂))
  compose-height-meta Θ (h₁ ⨾ m₁ ⨾ t₁) (h₂ ⨾ m₂ ⨾ t₂)
      | G ？ ℓ
      with m₁ | h₁
  ...   | err ℓ′ | _ = m≤m⊔n 1 (meta-middle-height m₂)
  ...   | id⋆ | id ⋆ = m≤n⊔m 1 (meta-middle-height m₂)
  ...   | id⋆ | G′ ？ ℓ′ = m≤m⊔n 1 (meta-middle-height m₂)
  ...   | id⋆ | id (` ι) = m≤m⊔n 1 (meta-middle-height m₂)
  ...   | id⋆ | id (A ⇒ B) = m≤m⊔n 1 (meta-middle-height m₂)
  ...   | id⋆ | id (Ref A) = m≤m⊔n 1 (meta-middle-height m₂)
  ...   | id⋆ | id (‶ O ″ ê) = m≤m⊔n 1 (meta-middle-height m₂)
  ...   | id⋆ | id (∀̇ A) = m≤m⊔n 1 (meta-middle-height m₂)
  ...   | id⋆ | id (e₁ <: e₂ => A) = m≤m⊔n 1 (meta-middle-height m₂)
  ...   | idι ι | _ = m≤m⊔n 1 (meta-middle-height m₂)
  ...   | c₁ ⇒ c₂ | _ =
    ≤-trans (pos-meta-middle-height (c₁ ⇒ c₂))
      (m≤m⊔n (meta-middle-height (c₁ ⇒ c₂)) (meta-middle-height m₂))
  ...   | ‶ cᵒ ″ cᵉ | _ =
    ≤-trans (pos-meta-middle-height (‶ cᵒ ″ cᵉ))
      (m≤m⊔n (meta-middle-height (‶ cᵒ ″ cᵉ)) (meta-middle-height m₂))
  ...   | ref c₁ c₂ | _ =
    ≤-trans (pos-meta-middle-height (ref c₁ c₂))
      (m≤m⊔n (meta-middle-height (ref c₁ c₂)) (meta-middle-height m₂))
  ...   | ∀̇ c | _ =
    ≤-trans (pos-meta-middle-height (∀̇ c))
      (m≤m⊔n (meta-middle-height (∀̇ c)) (meta-middle-height m₂))
  ...   | e₁ <: e₂ => c | _ =
    ≤-trans (pos-meta-middle-height (e₁ <: e₂ => c))
      (m≤m⊔n (meta-middle-height (e₁ <: e₂ => c)) (meta-middle-height m₂))
  compose-height-meta Θ (h₁ ⨾ m₁ ⨾ t₁) (h₂ ⨾ m₂ ⨾ t₂)
      | G ！
      with m₂ | is-error? m₁ | t₂
  ...   | err ℓ | yes (error {ℓ′}) | _ = m≤n⊔m (meta-middle-height m₁) 1
  ...   | err ℓ | no _ | _ = m≤n⊔m (meta-middle-height m₁) 1
  ...   | id⋆ | _ | id ⋆ = m≤m⊔n (meta-middle-height m₁) 1
  ...   | id⋆ | _ | G′ ！ = m≤m⊔n (meta-middle-height m₁) 1
  ...   | id⋆ | _ | id (` ι) = m≤m⊔n (meta-middle-height m₁) 1
  ...   | id⋆ | _ | id (A ⇒ B) = m≤m⊔n (meta-middle-height m₁) 1
  ...   | id⋆ | _ | id (Ref A) = m≤m⊔n (meta-middle-height m₁) 1
  ...   | id⋆ | _ | id (‶ O ″ ê) = m≤m⊔n (meta-middle-height m₁) 1
  ...   | id⋆ | _ | id (∀̇ A) = m≤m⊔n (meta-middle-height m₁) 1
  ...   | id⋆ | _ | id (e₁ <: e₂ => A) = m≤m⊔n (meta-middle-height m₁) 1
  ...   | idι ι | _ | _ = m≤m⊔n (meta-middle-height m₁) 1
  ...   | c₁ ⇒ c₂ | _ | _ =
    m≤m⊔n (meta-middle-height m₁) (meta-middle-height (c₁ ⇒ c₂))
  ...   | ‶ cᵒ ″ cᵉ | _ | _ =
    m≤m⊔n (meta-middle-height m₁) (meta-middle-height (‶ cᵒ ″ cᵉ))
  ...   | ref c₁ c₂ | _ | _ =
    m≤m⊔n (meta-middle-height m₁) (meta-middle-height (ref c₁ c₂))
  ...   | ∀̇ c | _ | _ =
    m≤m⊔n (meta-middle-height m₁) (meta-middle-height (∀̇ c))
  ...   | e₁ <: e₂ => c | _ | _ =
    m≤m⊔n (meta-middle-height m₁) (meta-middle-height (e₁ <: e₂ => c))
