module LambdaAlphaRefStar.Theories.CodeTypes where

open import Data.List using (List; []; _∷_; _∷ʳ_; drop; length; map)
open import Data.List.Relation.Unary.All using (All) renaming ([] to []ᴬ; _∷_ to _∷ᴬ_; map to All-map)
open import Data.List.Relation.Unary.All.Properties using (∷ʳ⁺; map⁺)
open import Data.Maybe using (Maybe; just; nothing; _>>=_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (∃-syntax; _×_; proj₁) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (inj₁; inj₂)
open import Function using (case_of_)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; subst; trans)
  renaming (sym to ≡-sym)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)

open import Utils using (_∋_; _∋_⦂_; _⊆_; _≼_; ≼-refl; ≼-snoc; Z; S_; here; there;
  drop-snoc; length-map; length-∷ʳ; lookup->member; lookup-snoc-inv; member->lookup; ⟨_,_,_⟩)
open import LambdaAlphaRefStar.Theories.EnvClassifiers
open import LambdaAlphaRefStar.Theories.BaseTypes using (Base; base-eq?)

infixr 6 _⇒_

-- | Object language types (S, T)
data OType : Set where
  `_  : Base → OType
  _⇒_ : OType → OType → OType

-- | Gradual object language types (O)
data OType⋆ : Set where
  ⋆   : OType⋆
  `_  : Base → OType⋆
  _⇒_ : OType⋆ → OType⋆ → OType⋆

data OGround : OType⋆ → Set where
  gbase : ∀ {ι} → OGround (` ι)
  gfun  : OGround (⋆ ⇒ ⋆)

infix 4 _↪ᵒ_

-- The static-view relation on code types. It extracts the static code type from
-- a gradual code type when the gradual type is fully static.
data _↪ᵒ_ : OType⋆ → OType → Set where

  `_  : ∀ ι → ` ι ↪ᵒ ` ι

  _⇒_ : ∀ {O₁ O₂ T₁ T₂}
    → O₁ ↪ᵒ T₁
    → O₂ ↪ᵒ T₂
      ------------------------
    → O₁ ⇒ O₂ ↪ᵒ T₁ ⇒ T₂

↪ᵒ-unique : ∀ {O T T′}
  → O ↪ᵒ T
  → O ↪ᵒ T′
    ---------------
  → T ≡ T′
↪ᵒ-unique (` ι) (` .ι) = refl
↪ᵒ-unique (O₁↪T₁ ⇒ O₂↪T₂) (O₁↪T₁′ ⇒ O₂↪T₂′)
  rewrite ↪ᵒ-unique O₁↪T₁ O₁↪T₁′ | ↪ᵒ-unique O₂↪T₂ O₂↪T₂′ = refl

_≡?ᵒ_ : (A B : OType⋆) → Dec (A ≡ B)
⋆ ≡?ᵒ ⋆ = yes refl
⋆ ≡?ᵒ (` _) = no λ ()
⋆ ≡?ᵒ (_ ⇒ _) = no λ ()
(` _) ≡?ᵒ ⋆ = no λ ()
(` x) ≡?ᵒ (` y) with base-eq? x y
... | yes refl = yes refl
... | no neq = no λ { refl → neq refl }
(` _) ≡?ᵒ (_ ⇒ _) = no λ ()
(_ ⇒ _) ≡?ᵒ ⋆ = no λ ()
(_ ⇒ _) ≡?ᵒ (` _) = no λ ()
(A ⇒ B) ≡?ᵒ (C ⇒ D) with A ≡?ᵒ C | B ≡?ᵒ D
... | yes refl | yes refl = yes refl
... | no neq | _ = no λ { refl → neq refl }
... | yes refl | no neq = no λ { refl → neq refl }

-- | Consistency on gradual code types
infix 4 _~ᵒ_

data _~ᵒ_ : OType⋆ → OType⋆ → Set where

  ~ᵒ-⋆-left : ∀ {O}
      ------------
    → ⋆ ~ᵒ O

  ~ᵒ-⋆-right : ∀ {O}
      ------------
    → O ~ᵒ ⋆

  ~ᵒ-base : ∀ {ι}
      ----------------
    → ` ι ~ᵒ ` ι

  ~ᵒ-fun : ∀ {O₁ O₁′ O₂ O₂′}
    → O₁ ~ᵒ O₁′
    → O₂ ~ᵒ O₂′
      -------------------------------
    → (O₁ ⇒ O₂) ~ᵒ (O₁′ ⇒ O₂′)


~ᵒ-sym : ∀ {O O′} → O ~ᵒ O′ → O′ ~ᵒ O
~ᵒ-sym ~ᵒ-⋆-left        = ~ᵒ-⋆-right
~ᵒ-sym ~ᵒ-⋆-right       = ~ᵒ-⋆-left
~ᵒ-sym ~ᵒ-base          = ~ᵒ-base
~ᵒ-sym (~ᵒ-fun O₁~O₁′ O₂~O₂′) = ~ᵒ-fun (~ᵒ-sym O₁~O₁′) (~ᵒ-sym O₂~O₂′)

-- | Object language typing contexts (Γᵒ).
--
-- An OCtx stores code variables in one shared list.  The cutoff is the
-- number of lexically-bound code variables at the front of that list.
-- The entries are the actual code-variable typings, each paired with the
-- EC variable that marks where the code variable is available.
record OCtx : Set where
  constructor octx
  field
    cutoff : ℕ
    entries : List (OType × ECVar)
    cutoff≤length : cutoff ≤ length entries

open OCtx public

infixl 5 _,_＠_
infixl 5 _,ᵍ_＠_
infix 4 _∋ᵒ_
infix 4 _∋ᵒ_⦂_

∅ᵒ : OCtx
∅ᵒ = octx zero [] z≤n

-- | Lexical binding conses a new entry and increments the cutoff.
_,_＠_ : OCtx → OType → ECVar → OCtx
Γᵒ , T ＠ α =
  octx (suc (Γᵒ .cutoff)) (⟨ T , α ⟩ ∷ Γᵒ .entries) (s≤s (Γᵒ .cutoff≤length))

-- | Runtime allocation appends a new global entry and leaves the cutoff unchanged.
-- | This makes sure the the (Γᵒ ∋ x ⦂ T @ α) lookup is stable.
_,ᵍ_＠_ : OCtx → OType → ECVar → OCtx
Γᵒ ,ᵍ T ＠ α =
  octx (Γᵒ .cutoff) (Γᵒ .entries ∷ʳ ⟨ T , α ⟩)
       (subst (Γᵒ .cutoff ≤_) (≡-sym (length-∷ʳ (Γᵒ .entries) _)) (m≤n⇒m≤1+n (Γᵒ .cutoff≤length)))

octx-cong : ∀ {k Γᵒ₁ Γᵒ₂ k≤len₁ k≤len₂}
  → Γᵒ₁ ≡ Γᵒ₂
    ---------------------------------------
  → octx k Γᵒ₁ k≤len₁ ≡ octx k Γᵒ₂ k≤len₂
octx-cong {k≤len₁ = k≤len₁} {k≤len₂ = k≤len₂} refl rewrite ≤-irrelevant k≤len₁ k≤len₂ = refl

freshᵒ : OCtx → ECVar
freshᵒ Γᵒ = length (Γᵒ .entries)

-- | Globally-allocated code variables are the entries after the lexical cutoff.
GlobalEntries : OCtx → List (OType × ECVar)
GlobalEntries Γᵒ = drop (Γᵒ .cutoff) (Γᵒ .entries)

-- | Unique owner invariant: if two entries have the same EC owner, then they
-- are the same entry position and have the same type.
UniqueOwner : List (OType × ECVar) → Set
UniqueOwner Γᵒ =
  ∀ {x y T₁ T₂ α} → Γᵒ ∋ x ⦂ ⟨ T₁ , α ⟩ → Γᵒ ∋ y ⦂ ⟨ T₂ , α ⟩ → x ≡ y × T₁ ≡ T₂

infix 4 _≼ᵒ_

-- | Code-context extension should preserve de Bruijn lookup and global entries.
record _≼ᵒ_ (Γᵒ₁ Γᵒ₂ : OCtx) : Set where
  constructor octx≼
  field
    entries≼ : Γᵒ₁ .entries ≼ Γᵒ₂ .entries
    globalEntries⊆ : GlobalEntries Γᵒ₁ ⊆ GlobalEntries Γᵒ₂

open _≼ᵒ_ public

≼ᵒ-refl : ∀ {Γᵒ} → Γᵒ ≼ᵒ Γᵒ
≼ᵒ-refl = octx≼ ≼-refl (λ member → member)

≼ᵒ-snoc : ∀ {Γᵒ T α}
    ------------------------
  → Γᵒ ≼ᵒ Γᵒ ,ᵍ T ＠ α
≼ᵒ-snoc {Γᵒ} = octx≼ (≼-snoc ≼-refl) (drop-snoc (Γᵒ .cutoff) (Γᵒ .entries))

lookupOwner : List (OType × ECVar) → ECVar → Maybe (ℕ × OType)
lookupOwner [] α = nothing
lookupOwner (⟨ T , β ⟩ ∷ Γᵒ) α with β ≟ α
... | yes _ = just ⟨ zero , T ⟩
... | no _ = do
  ⟨ x , U ⟩ ← lookupOwner Γᵒ α
  just ⟨ suc x , U ⟩

lookupOwner-here : ∀ {Γᵒ T α}
    ------------------------------------------------------
  → lookupOwner (⟨ T , α ⟩ ∷ Γᵒ) α ≡ just ⟨ zero , T ⟩
lookupOwner-here {α = α} with α ≟ α
... | yes refl = refl
... | no α≢α = contradiction refl α≢α

lookupOwner-wf : ∀ {Δ Γᵒ α x T}
  → All (λ { ⟨ _ , β ⟩ → β < Δ .size }) Γᵒ
  → lookupOwner Γᵒ α ≡ just ⟨ x , T ⟩
    ---------------------------------------------
  → α < Δ .size
lookupOwner-wf {Γᵒ = []} []ᴬ ()
lookupOwner-wf {Δ = Δ} {Γᵒ = ⟨ U , β ⟩ ∷ Γᵒ} {α = α} (β<Δ ∷ᴬ ⊢Γᵒ) owner with β ≟ α
... | yes refl = β<Δ
... | no _ with lookupOwner Γᵒ α in eq
... | nothing = contradiction owner (λ ())
... | just ⟨ x , V ⟩ = lookupOwner-wf {Δ = Δ} ⊢Γᵒ eq

lookupOwner-cons-miss : ∀ {Γᵒ α β x T S}
  → β ≢ α
  → lookupOwner Γᵒ α ≡ just ⟨ x , T ⟩
    ---------------------------------------------------------
  → lookupOwner (⟨ S , β ⟩ ∷ Γᵒ) α ≡ just ⟨ suc x , T ⟩
lookupOwner-cons-miss {Γᵒ = Γᵒ} {α = α} {β = β} β≢α owner with β ≟ α
... | yes β≡α = contradiction β≡α β≢α
... | no _ with lookupOwner Γᵒ α in eq
... | nothing = contradiction owner (λ ())
... | just ⟨ x , U ⟩ with owner
... | refl = refl

lookupOwner-cons-miss-inv : ∀ {Γᵒ α β x T S}
  → β ≢ α
  → lookupOwner (⟨ S , β ⟩ ∷ Γᵒ) α ≡ just ⟨ suc x , T ⟩
    ---------------------------------------------------------
  → lookupOwner Γᵒ α ≡ just ⟨ x , T ⟩
lookupOwner-cons-miss-inv {Γᵒ = Γᵒ} {α = α} {β = β} β≢α owner with β ≟ α
... | yes β≡α = contradiction β≡α β≢α
... | no _ with lookupOwner Γᵒ α in eq
... | nothing = contradiction owner (λ ())
... | just ⟨ x , U ⟩ with owner
... | refl = refl

unique-owner-tail : ∀ {Γᵒ : List (OType × ECVar)} {Tα}
  → UniqueOwner (Tα ∷ Γᵒ)
    ---------------------------
  → UniqueOwner Γᵒ
unique-owner-tail unique lookup₁ lookup₂ with unique (there lookup₁) (there lookup₂)
... | ⟨ refl , T≡U ⟩ = ⟨ refl , T≡U ⟩

-- | This is the lemma that relates the UniqueOwner invariant to lookupOwner.
lookupOwner-index : ∀ {Γᵒ : List (OType × ECVar)} {x T α}
  → UniqueOwner Γᵒ
  → Γᵒ ∋ x ⦂ ⟨ T , α ⟩
    ---------------------------------------
  → lookupOwner Γᵒ α ≡ just ⟨ x , T ⟩
lookupOwner-index {Γᵒ = []} unique ()
lookupOwner-index {Γᵒ = ⟨ T , α ⟩ ∷ Γᵒ} unique here =
  lookupOwner-here {Γᵒ = Γᵒ} {T = T} {α = α}
lookupOwner-index {Γᵒ = ⟨ R , β ⟩ ∷ Γᵒ} {α = α} unique (there lookup)
  with β ≟ α
... | yes refl = contradiction (proj₁ (unique here (there lookup))) (λ ())
... | no β≢α
  rewrite lookupOwner-index (unique-owner-tail unique) lookup = refl

lookupOwner-cons-miss-zero-impossible : ∀ {Γᵒ α β T S}
  → β ≢ α
    ---------------------------------------------------------
  → lookupOwner (⟨ S , β ⟩ ∷ Γᵒ) α ≢ just ⟨ zero , T ⟩
lookupOwner-cons-miss-zero-impossible {Γᵒ = Γᵒ} {α = α} {β = β} β≢α owner with β ≟ α
... | yes β≡α = contradiction β≡α β≢α
... | no _ with lookupOwner Γᵒ α
... | nothing = contradiction owner (λ ())
... | just ⟨ x , U ⟩ = contradiction owner (λ ())

_∋ᵒ_ : OCtx → OType × ECVar → Set
Γᵒ ∋ᵒ T＠α = Γᵒ .entries ∋ T＠α

_∋ᵒ_⦂_ : OCtx → ℕ → OType × ECVar → Set
Γᵒ ∋ᵒ x ⦂ T＠α = Γᵒ .entries ∋ x ⦂ T＠α

renᵉ-octx-entry : RenameEC → OType × ECVar → OType × ECVar
renᵉ-octx-entry ρ ⟨ T , α ⟩ = ⟨ T , ρ α ⟩

renᵉ-octx : RenameEC → OCtx → OCtx
renᵉ-octx ρ Γᵒ =
  octx (Γᵒ .cutoff) (map (renᵉ-octx-entry ρ) (Γᵒ .entries))
    (subst (Γᵒ .cutoff ≤_)
      (≡-sym (length-map (renᵉ-octx-entry ρ) (Γᵒ .entries)))
      (Γᵒ .cutoff≤length))

⇑ᵉ-octx : OCtx → OCtx
⇑ᵉ-octx = renᵉ-octx suc

-- | Well-formed object contexts
infix 4 _⊢_OCtx

_⊢_OCtx : ECCtx → OCtx → Set
Δ ⊢ Γᵒ OCtx =
  -- all EC variables are well-scoped
  All (λ { ⟨ _ , α ⟩ → α < Δ .size }) (Γᵒ .entries) ×
  -- and owner lookup in the global entries is unique
  UniqueOwner (GlobalEntries Γᵒ)

global-member-owner : ∀ {Δ Γᵒ T α}
  → Δ ⊢ Γᵒ OCtx
  → Γᵒ .cutoff ≡ zero
  → GlobalEntries Γᵒ ∋ ⟨ T , α ⟩
    ------------------------------------------------------
  → ∃[ x ] lookupOwner (Γᵒ .entries) α ≡ just ⟨ x , T ⟩
global-member-owner {Γᵒ = octx zero entries _} ⟨ _ , unique ⟩ refl member =
  case member->lookup member of λ where
  ⟨ x , lookup ⟩ → ⟨ x , lookupOwner-index unique lookup ⟩

octx-wf-suc : ∀ {Δ Γᵒ}
  → Δ ⊢ Γᵒ OCtx
    ---------------------------
  → Δ ,α ⊢ ⇑ᵉ-octx Γᵒ OCtx
octx-wf-suc {Δ = Δ} {Γᵒ = Γᵒ} ⟨ scoped , unique ⟩ =
  ⟨ scoped-suc {Δ = Δ} {Γᵒ = Γᵒ} scoped
  , ⇑ᵉ-pres-global-unique-owner (Γᵒ .cutoff) (Γᵒ .entries) unique
  ⟩
  where
  ⇑ᵉ-pres-unique-owner : ∀ {Γᵒ : List (OType × ECVar)}
    → UniqueOwner Γᵒ
    ------------------------------------------------
    → UniqueOwner (map (renᵉ-octx-entry suc) Γᵒ)
  ⇑ᵉ-pres-unique-owner {Γᵒ = Γᵒ} unique {α = zero} lookup₁ lookup₂ =
    contradiction lookup₁ lookup-map-suc-zero
    where
    lookup-map-suc-zero : ∀ {Γᵒ : List (OType × ECVar)} {x T}
      → ¬ (map (renᵉ-octx-entry suc) Γᵒ ∋ x ⦂ ⟨ T , zero ⟩)
    lookup-map-suc-zero {Γᵒ = []} ()
    lookup-map-suc-zero {Γᵒ = _ ∷ Γᵒ} (there lookup) = lookup-map-suc-zero lookup
  ⇑ᵉ-pres-unique-owner {Γᵒ = Γᵒ} unique {α = suc α} lookup₁ lookup₂ =
    unique (lookup-map-suc-inv lookup₁) (lookup-map-suc-inv lookup₂)
    where
    lookup-map-suc-inv : ∀ {Γᵒ : List (OType × ECVar)} {x T α}
      → map (renᵉ-octx-entry suc) Γᵒ ∋ x ⦂ ⟨ T , suc α ⟩
      → Γᵒ ∋ x ⦂ ⟨ T , α ⟩
    lookup-map-suc-inv {Γᵒ = []} ()
    lookup-map-suc-inv {Γᵒ = _ ∷ Γᵒ} here = here
    lookup-map-suc-inv {Γᵒ = _ ∷ Γᵒ} (there lookup) = there (lookup-map-suc-inv lookup)

  ⇑ᵉ-pres-global-unique-owner : ∀ k (Γᵒ : List (OType × ECVar))
    → UniqueOwner (drop k Γᵒ)
    → UniqueOwner (drop k (map (renᵉ-octx-entry suc) Γᵒ))
  ⇑ᵉ-pres-global-unique-owner zero Γᵒ nodup = ⇑ᵉ-pres-unique-owner nodup
  ⇑ᵉ-pres-global-unique-owner (suc k) [] nodup ()
  ⇑ᵉ-pres-global-unique-owner (suc k) (_ ∷ Γᵒ) nodup = ⇑ᵉ-pres-global-unique-owner k Γᵒ nodup

  scoped-suc : ∀ {Δ Γᵒ}
    → All (λ { ⟨ _ , α ⟩ → α < Δ .size }) (Γᵒ .entries)
      ----------------------------------------------------
    → All (λ { ⟨ _ , α ⟩ → α < suc (Δ .size) })
          (map (renᵉ-octx-entry suc) (Γᵒ .entries))
  scoped-suc scoped = map⁺ (All-map s≤s scoped)

octx-wf-global-ext : ∀ {Δ Γᵒ T}
  → Δ ⊢ Γᵒ OCtx
    --------------------------------------------
  → Δ ,ᵍα ⊢ Γᵒ ,ᵍ T ＠ freshᵉ Δ OCtx
octx-wf-global-ext {Δ = Δ} {Γᵒ = Γᵒ} {T = T} ⟨ scoped , unique ⟩ =
  ⟨ ∷ʳ⁺ (scoped-weaken scoped) (s≤s ≤-refl)
  , unique-owner-global-snoc (Γᵒ .cutoff) (Γᵒ .entries) unique
      (no-fresh-owner-drop (Γᵒ .cutoff) {Δ = Δ} {Γᵒ = Γᵒ .entries} scoped)
  ⟩
  where
  scoped-weaken : ∀ {entries}
    → All (λ { ⟨ _ , α ⟩ → α < Δ .size }) entries
      ------------------------------------------------
    → All (λ { ⟨ _ , α ⟩ → α < suc (Δ .size) }) entries
  scoped-weaken []ᴬ = []ᴬ
  scoped-weaken (α<Δ ∷ᴬ scoped) =
    m≤n⇒m≤1+n {m = suc _} {n = Δ .size} α<Δ ∷ᴬ scoped-weaken scoped

  unique-owner-snoc : ∀ {Γᵒ : List (OType × ECVar)} {T : OType} {α : ECVar}
    → UniqueOwner Γᵒ
    → (∀ {U} → ¬ Γᵒ ∋ ⟨ U , α ⟩)
      ----------------------------------------
    → UniqueOwner (Γᵒ ∷ʳ ⟨ T , α ⟩)
  unique-owner-snoc {Γᵒ = Γᵒ} {T = T} {α = α} unique noOld lookup₁ lookup₂
    with lookup-snoc-inv {xs = Γᵒ} lookup₁ | lookup-snoc-inv {xs = Γᵒ} lookup₂
  ... | inj₁ old₁ | inj₁ old₂ = unique old₁ old₂
  ... | inj₁ old₁ | inj₂ ⟨ _ , refl ⟩ = contradiction (lookup->member old₁) noOld
  ... | inj₂ ⟨ _ , refl ⟩ | inj₁ old₂ = contradiction (lookup->member old₂) noOld
  ... | inj₂ ⟨ x≡length , refl ⟩ | inj₂ ⟨ y≡length , refl ⟩ = ⟨ trans x≡length (≡-sym y≡length) , refl ⟩

  unique-owner-global-snoc : ∀ k (Γᵒ : List (OType × ECVar)) {T : OType} {α : ECVar}
    → UniqueOwner (drop k Γᵒ)
    → (∀ {U} → ¬ (drop k Γᵒ ∋ ⟨ U , α ⟩))
      ------------------------------------------------
    → UniqueOwner (drop k (Γᵒ ∷ʳ ⟨ T , α ⟩))
  unique-owner-global-snoc zero Γᵒ nodup noOld = unique-owner-snoc nodup noOld
  unique-owner-global-snoc (suc zero) [] nodup noOld ()
  unique-owner-global-snoc (suc (suc k)) [] nodup noOld ()
  unique-owner-global-snoc (suc k) (_ ∷ Γᵒ) nodup noOld = unique-owner-global-snoc k Γᵒ nodup noOld

  no-fresh-owner-drop : ∀ k {Δ} {Γᵒ : List (OType × ECVar)}
    → All (λ { ⟨ _ , α ⟩ → α < Δ .size }) Γᵒ
      ------------------------------------------------------
    → ∀ {T} → ¬ (drop k Γᵒ ∋ ⟨ T , freshᵉ Δ ⟩)
  no-fresh-owner-drop zero {Δ = Δ} {Γᵒ = []} []ᴬ ()
  no-fresh-owner-drop zero {Δ = Δ} {Γᵒ = ⟨ T , α ⟩ ∷ Γᵒ} (α<Δ ∷ᴬ ⊢Γᵒ) Z = wf-var-≢fresh {Δ = Δ} α<Δ refl
  no-fresh-owner-drop zero {Δ = Δ} {Γᵒ = ⟨ T , α ⟩ ∷ Γᵒ} (α<Δ ∷ᴬ ⊢Γᵒ) (S member) = no-fresh-owner-drop zero {Δ = Δ} {Γᵒ = Γᵒ} ⊢Γᵒ member
  no-fresh-owner-drop (suc k) {Δ = Δ} {Γᵒ = []} []ᴬ ()
  no-fresh-owner-drop (suc k) {Δ = Δ} {Γᵒ = _ ∷ Γᵒ} (_ ∷ᴬ ⊢Γᵒ) member = no-fresh-owner-drop k {Δ = Δ} {Γᵒ = Γᵒ} ⊢Γᵒ member

lookupOwner-⇑ᵉ : ∀ Γᵒ α
    ---------------------------------------------------------------------------
  → lookupOwner (map (renᵉ-octx-entry suc) Γᵒ) (suc α) ≡ lookupOwner Γᵒ α
lookupOwner-⇑ᵉ [] α = refl
lookupOwner-⇑ᵉ (⟨ T , β ⟩ ∷ Γᵒ) α with β ≟ α | suc β ≟ suc α
... | yes refl | yes _ = refl
... | yes refl | no sucβ≢sucβ = contradiction refl sucβ≢sucβ
... | no β≢α | yes sucβ≡sucα = contradiction (suc-inj sucβ≡sucα) β≢α
  where
  suc-inj : ∀ {m n} → suc m ≡ suc n → m ≡ n
  suc-inj refl = refl
... | no _ | no _ rewrite lookupOwner-⇑ᵉ Γᵒ α = refl

lookupOwner-⇑ᵉ-zero : ∀ Γᵒ
    ------------------------------------------------------------
  → lookupOwner (map (renᵉ-octx-entry suc) Γᵒ) zero ≡ nothing
lookupOwner-⇑ᵉ-zero [] = refl
lookupOwner-⇑ᵉ-zero (⟨ T , α ⟩ ∷ Γᵒ) with suc α ≟ zero
... | yes ()
... | no _ rewrite lookupOwner-⇑ᵉ-zero Γᵒ = refl
