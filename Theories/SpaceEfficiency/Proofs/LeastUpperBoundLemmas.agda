module Theories.SpaceEfficiency.Proofs.LeastUpperBoundLemmas where

open import Data.Nat using (_≤_; _⊔_)
open import Data.Nat.Properties using
  (≤-refl; ≤-trans; ≤-reflexive; m≤m⊔n; m≤n⊔m; ⊔-assoc; ⊔-comm; ⊔-commutativeSemigroup; ⊔-lub)
open import Algebra.Properties.CommutativeSemigroup ⊔-commutativeSemigroup
  using (x∙yz≈y∙xz)
open import Relation.Binary.PropositionalEquality using (sym)

open Data.Nat.Properties.≤-Reasoning


⊔-swap-middle≤ : ∀ a b c → a ⊔ (b ⊔ c) ≤ b ⊔ (a ⊔ c)
⊔-swap-middle≤ a b c = ≤-reflexive (x∙yz≈y∙xz a b c)

⊔-comm≤ : ∀ a b → a ⊔ b ≤ b ⊔ a
⊔-comm≤ a b = ≤-reflexive (⊔-comm a b)

⊔-mono≤ : ∀ {a b c d}
  → a ≤ b
  → c ≤ d
  → a ⊔ c ≤ b ⊔ d
⊔-mono≤ {b = b} {d = d} a≤b c≤d =
  ⊔-lub
    (≤-trans a≤b (m≤m⊔n b d))
    (≤-trans c≤d (m≤n⊔m b d))

⊔-assoc≤ : ∀ a b c → a ⊔ (b ⊔ c) ≤ (a ⊔ b) ⊔ c
⊔-assoc≤ a b c = ≤-reflexive (sym (⊔-assoc a b c))

⊔-assocʳ≤ : ∀ a b c → (a ⊔ b) ⊔ c ≤ a ⊔ (b ⊔ c)
⊔-assocʳ≤ a b c = ≤-reflexive (⊔-assoc a b c)

⊔-add-right≤ : ∀ {a b c d e}
  → a ⊔ b ≤ c ⊔ d
  → a ⊔ (b ⊔ e) ≤ c ⊔ (d ⊔ e)
⊔-add-right≤ {a} {b} {c} {d} {e} ab≤cd =
  begin
    a ⊔ (b ⊔ e)
  ≤⟨ ⊔-assoc≤ a b e ⟩
    (a ⊔ b) ⊔ e
  ≤⟨ ⊔-mono≤ ab≤cd ≤-refl ⟩
    (c ⊔ d) ⊔ e
  ≤⟨ ⊔-assocʳ≤ c d e ⟩
    c ⊔ (d ⊔ e)
  ∎

⊔-add-middle≤ : ∀ {a b c d e}
  → a ⊔ b ≤ c ⊔ d
  → a ⊔ (e ⊔ b) ≤ c ⊔ (e ⊔ d)
⊔-add-middle≤ {a} {b} {c} {d} {e} ab≤cd =
  ⊔-lub
    (≤-trans (m≤m⊔n a b) (≤-trans ab≤cd cd≤ced))
    (⊔-lub
      (≤-trans (m≤m⊔n e d) (m≤n⊔m c (e ⊔ d)))
      (≤-trans (m≤n⊔m a b) (≤-trans ab≤cd cd≤ced)))
  where
    cd≤ced : c ⊔ d ≤ c ⊔ (e ⊔ d)
    cd≤ced =
      ⊔-lub
        (m≤m⊔n c (e ⊔ d))
        (≤-trans (m≤n⊔m e d) (m≤n⊔m c (e ⊔ d)))

⊔-combine≤ : ∀ {a b c d h}
  → a ≤ c ⊔ h
  → b ≤ d ⊔ h
  → a ⊔ b ≤ (c ⊔ d) ⊔ h
⊔-combine≤ {c = c} {d = d} {h = h} a≤ b≤ =
  ⊔-lub
    (≤-trans a≤ c⊔h≤)
    (≤-trans b≤ d⊔h≤)
  where
    c⊔h≤ : c ⊔ h ≤ (c ⊔ d) ⊔ h
    c⊔h≤ =
      ⊔-lub
        (≤-trans (m≤m⊔n c d) (m≤m⊔n (c ⊔ d) h))
        (m≤n⊔m (c ⊔ d) h)

    d⊔h≤ : d ⊔ h ≤ (c ⊔ d) ⊔ h
    d⊔h≤ =
      ⊔-lub
        (≤-trans (m≤n⊔m c d) (m≤m⊔n (c ⊔ d) h))
        (m≤n⊔m (c ⊔ d) h)
