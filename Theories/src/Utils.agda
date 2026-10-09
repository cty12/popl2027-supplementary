module Utils where

open import Data.List
open import Data.List.Relation.Unary.All using (All) renaming (_∷_ to _∷ᴬ_)
open import Data.Product using (∃-syntax; _×_) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Maybe using (Maybe; just; nothing) renaming (_>>=_ to _bind_)
open import Data.Nat
open import Data.Bool using (Bool; true; false; if_then_else_; _∧_)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; subst; cong)
open import Function using (case_of_)
open import Agda.Builtin.String

≡ᵇ-refl : ∀ x → (x ≡ᵇ x) ≡ true
≡ᵇ-refl zero = refl
≡ᵇ-refl (suc x) = ≡ᵇ-refl x


record Eq (A : Set) : Set₁ where
  field
    _==_ : A → A → Bool

open Eq ⦃...⦄ using (_==_)

nth : ∀ {A : Set} → List A → ℕ → Maybe A
nth []       _       = nothing
nth (x ∷ ls) zero    = just x
nth (x ∷ ls) (suc k) = nth ls k

index : ∀ {A : Set} ⦃ eqA : Eq A ⦄ → List A → (a : A) → Maybe ℕ
index [] a = nothing
index (a ∷ as) b =
  if a == b then just 0
    else (index as b bind λ i → just (suc i))


data NonEmpty {A : Set} : List A → Set where

  nonempty : ∀ {x xs}
      -------------------
    → NonEmpty (x ∷ xs)

nonempty-++ : ∀ {A : Set} {xs ys : List A}
  → NonEmpty xs
    --------------------
  → NonEmpty (xs ++ ys)
nonempty-++ nonempty = nonempty


infix 4 _∋_

data _∋_ {A : Set} : List A → A → Set where

  Z : ∀ {Γ : List A} {x}
    → x ∷ Γ ∋ x

  S_ : ∀ {Γ : List A} {x y}
    → Γ ∋ x
    → y ∷ Γ ∋ x

member? : ∀ {A : Set}
  → (∀ (x y : A) → Dec (x ≡ y))
  → (xs : List A)
  → (x : A)
    ------------------------
  → Dec (xs ∋ x)
member? _≟_ [] x = no λ ()
member? _≟_ (y ∷ xs) x with x ≟ y
... | yes refl = yes Z
... | no x≢y with member? _≟_ xs x
...   | yes x∈xs = yes (S x∈xs)
...   | no  x∉xs = no λ { Z → x≢y refl ; (S x∈xs) → x∉xs x∈xs }

delete : ∀ {A : Set}
  → (xs : List A)
  → (x : A)
  → xs ∋ x
    ------------------
  → List A
delete (_ ∷ xs) x Z = xs
delete (y ∷ xs) x (S x∈xs) = y ∷ delete xs x x∈xs

length-delete : ∀ {A : Set} {xs : List A} {x}
  → (x∈xs : xs ∋ x)
    ------------------------------------------------
  → suc (length (delete xs x x∈xs)) ≡ length xs
length-delete Z = refl
length-delete (S x∈xs) = cong suc (length-delete x∈xs)

delete-preserves : ∀ {A : Set} {xs : List A} {x y}
  → (x∈xs : xs ∋ x)
  → xs ∋ y
  → y ≢ x
    ---------------------------
  → delete xs x x∈xs ∋ y
delete-preserves Z Z y≢x = contradiction refl y≢x
delete-preserves Z (S y∈xs) y≢x = y∈xs
delete-preserves (S x∈xs) Z y≢x = Z
delete-preserves (S x∈xs) (S y∈xs) y≢x = S (delete-preserves x∈xs y∈xs y≢x)

infix 0 _⊆_

_⊆_ : ∀ {A : Set} → List A → List A → Set
xs ⊆ ys = ∀ {x} → xs ∋ x → ys ∋ x

NoDup : ∀ {A : Set} → List A → Set
NoDup [] = ⊤
NoDup (x ∷ xs) = ¬ (xs ∋ x) × NoDup xs

subset-length : ∀ {A : Set} {xs ys : List A}
  → NoDup xs
  → xs ⊆ ys
    ---------------------------
  → length xs ≤ length ys
subset-length {xs = []} tt xs⊆ys = z≤n
subset-length {xs = x ∷ xs} ⟨ x∉xs , nodup ⟩ xs⊆ys =
  subst (suc (length xs) ≤_)
    (length-delete (xs⊆ys Z))
    (s≤s
      (subset-length nodup
        (λ y∈xs →
          delete-preserves (xs⊆ys Z) (xs⊆ys (S y∈xs)) (λ {refl → x∉xs y∈xs}))))

lookup-all : ∀ {A : Set} {P : A → Set} {xs x}
  → All P xs
  → xs ∋ x
    ---------------
  → P x
lookup-all (px ∷ᴬ _) Z = px
lookup-all (_ ∷ᴬ pxs) (S x∈xs) = lookup-all pxs x∈xs

infix 4 _∋_⦂_

data _∋_⦂_ {A : Set} : List A → ℕ → A → Set where

  here : ∀ {Γ x}
      -------------------
    → (x ∷ Γ) ∋ zero ⦂ x

  there : ∀ {Γ x y n}
    → Γ ∋ n ⦂ x
      ------------------------
    → (y ∷ Γ) ∋ suc n ⦂ x

lookup->member : ∀ {A : Set} {Γ : List A} {n x}
  → Γ ∋ n ⦂ x
    ---------
  → Γ ∋ x
lookup->member {Γ = []} ()
lookup->member here = Z
lookup->member (there lookup) = S (lookup->member lookup)

lookup-map : ∀ {A B : Set} {Γ : List A} {n x} {f : A → B}
  → Γ ∋ n ⦂ x
    ---------------------
  → map f Γ ∋ n ⦂ f x
lookup-map here = here
lookup-map (there lookup) = there (lookup-map lookup)

lookup-map-inv : ∀ {A B : Set} {Γ : List A} {n y} {f : A → B}
  → map f Γ ∋ n ⦂ y
    ----------------------------------
  → ∃[ x ] (Γ ∋ n ⦂ x) × (f x ≡ y)
lookup-map-inv {Γ = []} ()
lookup-map-inv {Γ = _ ∷ _} here = ⟨ _ , ⟨ here , refl ⟩ ⟩
lookup-map-inv {Γ = _ ∷ _} (there lookup) with lookup-map-inv lookup
... | ⟨ x , ⟨ lookup′ , refl ⟩ ⟩ = ⟨ x , ⟨ there lookup′ , refl ⟩ ⟩

member-map : ∀ {A B : Set} {Γ : List A} {x} {f : A → B}
  → Γ ∋ x
    ---------
  → map f Γ ∋ f x
member-map Z = Z
member-map (S member) = S (member-map member)

member-map-inv : ∀ {A B : Set} {Γ : List A} {y} {f : A → B}
  → map f Γ ∋ y
    -------------------------------
  → ∃[ x ] (Γ ∋ x) × (f x ≡ y)
member-map-inv {Γ = []} ()
member-map-inv {Γ = _ ∷ _} Z = ⟨ _ , ⟨ Z , refl ⟩ ⟩
member-map-inv {Γ = _ ∷ _} (S member) with member-map-inv member
... | ⟨ x , ⟨ member′ , refl ⟩ ⟩ = ⟨ x , ⟨ S member′ , refl ⟩ ⟩

length-map : ∀ {A B : Set} (f : A → B) (xs : List A)
  → length (map f xs) ≡ length xs
length-map f [] = refl
length-map f (_ ∷ xs) = cong suc (length-map f xs)

member->lookup : ∀ {A : Set} {Γ : List A} {x}
  → Γ ∋ x
    -------------------
  → ∃[ n ] Γ ∋ n ⦂ x
member->lookup {Γ = []} ()
member->lookup Z = ⟨ zero , here ⟩
member->lookup (S member) with member->lookup member
... | ⟨ n , lookup ⟩ = ⟨ suc n , there lookup ⟩

∋-∷ʳ : ∀ {A : Set} {xs : List A} {x y}
  → xs ∋ x
    -------------
  → xs ∷ʳ y ∋ x
∋-∷ʳ {xs = []} ()
∋-∷ʳ {xs = _ ∷ _} Z = Z
∋-∷ʳ {xs = _ ∷ xs} (S x) = S (∋-∷ʳ x)

∋-∷ʳ-last : ∀ {A : Set} (xs : List A) {x}
    -------------------
  → xs ∷ʳ x ∋ x
∋-∷ʳ-last [] = Z
∋-∷ʳ-last (_ ∷ xs) = S (∋-∷ʳ-last xs)

member-snoc-inv : ∀ {A : Set} {xs : List A} {x y}
  → xs ∷ʳ y ∋ x
    --------------------
  → (xs ∋ x) ⊎ (x ≡ y)
member-snoc-inv {xs = []} Z = inj₂ refl
member-snoc-inv {xs = []} (S ())
member-snoc-inv {xs = _ ∷ _} Z = inj₁ Z
member-snoc-inv {xs = _ ∷ xs} (S member) with member-snoc-inv {xs = xs} member
... | inj₁ old = inj₁ (S old)
... | inj₂ refl = inj₂ refl

length-∷ʳ : ∀ {A : Set} (xs : List A) (x : A)
  → length (xs ∷ʳ x) ≡ suc (length xs)
length-∷ʳ [] x = refl
length-∷ʳ (_ ∷ xs) x = cong suc (length-∷ʳ xs x)

member-map-drop : ∀ {A B : Set} (f : A → B) (k : ℕ) (xs : List A) {x}
  → drop k xs ∋ x
    -------------------------
  → drop k (map f xs) ∋ f x
member-map-drop f zero xs x∈ = member-map x∈
member-map-drop f (suc k) [] ()
member-map-drop f (suc k) (_ ∷ xs) x∈ = member-map-drop f k xs x∈

member-map-drop-inv : ∀ {A B : Set} (f : A → B) (k : ℕ) (xs : List A) {y}
  → drop k (map f xs) ∋ y
    ----------------------------------------------
  → ∃[ x ] (drop k xs ∋ x) × (f x ≡ y)
member-map-drop-inv f zero xs y∈ = member-map-inv y∈
member-map-drop-inv f (suc k) [] ()
member-map-drop-inv f (suc k) (_ ∷ xs) y∈ = member-map-drop-inv f k xs y∈

drop-snoc : ∀ {A : Set} (k : ℕ) (xs : List A) {x y}
  → drop k xs ∋ x
    --------------------
  → drop k (xs ∷ʳ y) ∋ x
drop-snoc zero xs x∈ = ∋-∷ʳ x∈
drop-snoc (suc k) [] ()
drop-snoc (suc k) (_ ∷ xs) x∈ = drop-snoc k xs x∈

drop-snoc-last : ∀ {A : Set} (k : ℕ) (xs : List A) {x}
  → k ≤ length xs
    ----------------------
  → drop k (xs ∷ʳ x) ∋ x
drop-snoc-last zero xs k≤len = ∋-∷ʳ-last xs
drop-snoc-last (suc k) [] ()
drop-snoc-last (suc k) (_ ∷ xs) (s≤s k≤len) = drop-snoc-last k xs k≤len

lookup-snoc : ∀ {A : Set} {Γ : List A} {x y n}
  → Γ ∋ n ⦂ x
    ------------------
  → Γ ∷ʳ y ∋ n ⦂ x
lookup-snoc {Γ = []} ()
lookup-snoc {Γ = _ ∷ _} here = here
lookup-snoc {Γ = _ ∷ Γ} (there Γ∋x) = there (lookup-snoc Γ∋x)

lookup-snoc-inv : ∀ {A : Set} {xs : List A} {n x y}
  → xs ∷ʳ y ∋ n ⦂ x
    ------------------------------------------
  → (xs ∋ n ⦂ x) ⊎ (n ≡ length xs × x ≡ y)
lookup-snoc-inv {xs = []} here = inj₂ ⟨ refl , refl ⟩
lookup-snoc-inv {xs = []} (there ())
lookup-snoc-inv {xs = _ ∷ xs} here = inj₁ here
lookup-snoc-inv {xs = _ ∷ xs} (there lookup) with lookup-snoc-inv {xs = xs} lookup
... | inj₁ old = inj₁ (there old)
... | inj₂ ⟨ n≡length , x≡y ⟩ = inj₂ ⟨ cong suc n≡length , x≡y ⟩

infix 4 _≼_

_≼_ : ∀ {A : Set} → List A → List A → Set
xs ≼ ys = ∀ {n x} → xs ∋ n ⦂ x → ys ∋ n ⦂ x

≼-refl : ∀ {A : Set} {xs : List A}
    --------
  → xs ≼ xs
≼-refl lookup = lookup

≼-snoc : ∀ {A : Set} {xs ys : List A} {y}
  → xs ≼ ys
    -------------
  → xs ≼ ys ∷ʳ y
≼-snoc xs≼ys lookup = lookup-snoc (xs≼ys lookup)

≼-member : ∀ {A : Set} {xs ys : List A} {x}
  → xs ≼ ys
  → xs ∋ x
    ------
  → ys ∋ x
≼-member xs≼ys member with member->lookup member
... | ⟨ n , lookup ⟩ = lookup->member (xs≼ys lookup)

∋-snoc-last : ∀ {A : Set} (Γ : List A) {x}
    -----------------------------
  → Γ ∷ʳ x ∋ length Γ ⦂ x
∋-snoc-last [] = here
∋-snoc-last (_ ∷ Γ) = there (∋-snoc-last Γ)


{- Works on association lists -}
locate : ∀ {K V : Set} → (∀ (k₁ k₂ : K) → Dec (k₁ ≡ k₂)) → List (K × V) → K → Maybe V
locate _≟_ [] _ = nothing
locate _≟_ (⟨ k₀ , v₀ ⟩ ∷ l) k =
  case k ≟ k₀ of λ where
    (yes _) → just v₀
    (no  _) → locate _≟_ l k

assoc : ∀ {A B : Set} ⦃ eqA : Eq A ⦄ → List (A × B) → A → Maybe B
assoc [] _ = nothing
assoc (⟨ a , b ⟩ ∷ rest) c = if a == c then just b else assoc rest c

snoc-here : ∀ {X} (x : X) → ∀ xs → nth (xs ∷ʳ x) (length xs) ≡ just x
snoc-here x [] = refl
snoc-here x (_ ∷ xs) = snoc-here x xs

snoc-there : ∀ {X} (x : X) → ∀ xs {n y} → nth (xs ∷ʳ y) n ≡ just x → n ≢ length xs → nth xs n ≡ just x
snoc-there x [] {zero} refl neq = contradiction refl neq
snoc-there x (y ∷ xs) {zero} eq neq = eq
snoc-there x (y ∷ xs) {suc n} eq neq = snoc-there x xs eq n≢len
  where
  n≢len : n ≢ length xs
  n≢len n≡len = contradiction (cong suc n≡len) neq


length-∷-≤ : ∀ {A : Set} (x : A) (xs : List A) → length xs ≤ length (x ∷ xs)
length-∷-≤ x [] = z≤n
length-∷-≤ x (y ∷ xs) = s≤s (length-∷-≤ x xs)

pattern ⟨_,_,_⟩ x y z = ⟨ x , ⟨ y , z ⟩ ⟩
pattern ⟨_,_,_,_⟩ x y z w = ⟨ x , ⟨ y , ⟨ z , w ⟩ ⟩ ⟩
pattern ⟨_,_,_,_,_⟩ x y z w u = ⟨ x , ⟨ y , ⟨ z , ⟨ w , u ⟩ ⟩ ⟩ ⟩
pattern ⟨_,_,_,_,_,_⟩ x y z w u v = ⟨ x , ⟨ y , ⟨ z , ⟨ w , ⟨ u , v ⟩ ⟩ ⟩ ⟩ ⟩
pattern ⟨_,_,_,_,_,_,_⟩ x y z w u v p = ⟨ x , ⟨ y , ⟨ z , ⟨ w , ⟨ u , ⟨ v , p ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
pattern ⟨_,_,_,_,_,_,_,_⟩ x y z w u v p q = ⟨ x , ⟨ y , ⟨ z , ⟨ w , ⟨ u , ⟨ v , ⟨ p , q ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
pattern ⟨_,_,_,_,_,_,_,_,_⟩ x y z w u v p q i = ⟨ x , ⟨ y , ⟨ z , ⟨ w , ⟨ u , ⟨ v , ⟨ p , ⟨ q , i ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
pattern ⟨_,_,_,_,_,_,_,_,_,_⟩ x y z w u v p q i j = ⟨ x , ⟨ y , ⟨ z , ⟨ w , ⟨ u , ⟨ v , ⟨ p , ⟨ q , ⟨ i , j ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
pattern ⟨_,_,_,_,_,_,_,_,_,_,_⟩ x y z w u v p q i j k = ⟨ x , ⟨ y , ⟨ z , ⟨ w , ⟨ u , ⟨ v , ⟨ p , ⟨ q , ⟨ i , ⟨ j , k ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
pattern ⟨_,_,_,_,_,_,_,_,_,_,_,_⟩ x y z w u v p q i j k m = ⟨ x , ⟨ y , ⟨ z , ⟨ w , ⟨ u , ⟨ v , ⟨ p , ⟨ q , ⟨ i , ⟨ j , ⟨ k , m ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩


pattern ∅ = []
pattern [_,_] y z = y ∷ z ∷ []
pattern [_,_,_] x y z = x ∷ y ∷ z ∷ []
pattern [_,_,_,_] w x y z = w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_] v w x y z = v ∷ w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_,_] u v w x y z = u ∷ v ∷ w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_,_,_] u v w x y z p = u ∷ v ∷ w ∷ x ∷ y ∷ z ∷ p ∷ []
pattern [_,_,_,_,_,_,_,_] u v w x y z p q = u ∷ v ∷ w ∷ x ∷ y ∷ z ∷ p ∷ q ∷ []


instance
  EqNat : Eq ℕ
  EqNat ._==_ = _≡ᵇ_

instance
  EqStr : Eq String
  EqStr ._==_ = primStringEquality

eqList : ∀ {A : Set} ⦃ eqA : Eq A ⦄ → (xs ys : List A) → Bool
eqList [] [] = true
eqList [] (x ∷ _) = false
eqList (x ∷ _) [] = false
eqList (x ∷ xs) (y ∷ ys) = (x == y) ∧ eqList xs ys

instance
  EqList : ∀ {A : Set} ⦃ eqA : Eq A ⦄ → Eq (List A)
  EqList ._==_ = eqList


postulate
  extensionality : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} {f g : A → B}
    → (∀ (x : A) → f x ≡ g x)
      ---------------------------
    → f ≡ g
