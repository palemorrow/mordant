module Mordant.Word where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _<_; _≤_; _≡ᵇ_; _<ᵇ_; _≤ᵇ_; z≤n; s≤s; z<s; s<s)
open import Data.Nat.Properties
  using
  ( +-mono-≤-<; +-mono-≤; +-suc; +-identityʳ
  ; *-mono-≤; *-distribʳ-+; *-identityˡ
  ; ≤-refl; ≤-trans; ≤-irrelevant; <-irrelevant
  ; <-trans; ≤-<-trans; <-≤-trans; <⇒≤; <-cmp; ≮⇒≥; m≤m+n
  ; +-cancelˡ-≡; +-cancelˡ-<; +-cancelˡ-≤
  ; ^-distribˡ-+-*; <-asym; <-irrefl; ≡ᵇ⇒≡; ≡⇒≡ᵇ; <ᵇ⇒<; <⇒<ᵇ; ≤ᵇ⇒≤; ≤⇒≤ᵇ
  )
open import Data.Nat.DivMod using (_%_; _/_; m%n<n; m/n<m)
open import Data.Product using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Product.Properties using (Σ-≡,≡→≡)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary using (¬_)
open import Relation.Binary using (Tri)
open import Data.Nat.Induction using (<-rec)

two32 : ℕ
two32 = 2 ^ 32

two64 : ℕ
two64 = 2 ^ 64

Word32 : Set
Word32 = Σ ℕ (λ n → n < two32)

Word64 : Set
Word64 = Word32 × Word32

to32 : Word32 → ℕ
to32 = proj₁

to64 : Word64 → ℕ
to64 ((h , _) , (l , _)) = h * two32 + l

w32 : ℕ → Word32
w32 n = n % two32 , m%n<n n two32

w64 : ℕ → ℕ → Word64
w64 h l = w32 h , w32 l

_==32_ : Word32 → Word32 → Bool
x ==32 y = to32 x ≡ᵇ to32 y

_<32_ : Word32 → Word32 → Bool
x <32 y = to32 x <ᵇ to32 y

_≤32_ : Word32 → Word32 → Bool
x ≤32 y = to32 x ≤ᵇ to32 y

_&_ : ℕ → ℕ → ℕ
_&_ = <-rec (λ _ → ℕ → ℕ) helper
  where
  helper : ∀ x → (∀ {y} → y < x → ℕ → ℕ) → ℕ → ℕ
  helper zero ih y = zero
  helper (suc x) ih y =
    ((suc x) % 2) * (y % 2) + 2 * ih (m/n<m (suc x) 2 (s<s z<s)) (y / 2)

to32-< : ∀ (w : Word32) → to32 w < two32
to32-< (_ , p) = p

w32-value : ∀ n → to32 (w32 n) ≡ n % two32
w32-value n = refl


mul-suc-gen : ∀ b h → h * b + b ≡ (h + 1) * b
mul-suc-gen b h =
  trans (sym (cong (h * b +_) (*-identityˡ b))) (sym (*-distribʳ-+ b h 1))

h+1≡suc : ∀ h → h + 1 ≡ suc h
h+1≡suc h = trans (+-suc h 0) (cong suc (+-identityʳ h))

suc-le : ∀ b h → suc h ≤ b → h + 1 ≤ b
suc-le b h p = subst (λ z → z ≤ b) (sym (h+1≡suc h)) p

hi<→to64<-gen : ∀ b {hx hy lx ly} → lx < b → hx < hy → hx * b + lx < hy * b + ly
hi<→to64<-gen b {hx} {hy} {lx} {ly} lxb hx<hy =
  <-≤-trans
    (subst (λ z → hx * b + lx < z) (mul-suc-gen b hx) (+-mono-≤-< ≤-refl lxb))
    (≤-trans (*-mono-≤ (suc-le hy hx hx<hy) ≤-refl) (m≤m+n (hy * b) ly))

split-bound-gen : ∀ b h l → h < b → l < b → h * b + l < b * b
split-bound-gen b h l h< l< =
  <-≤-trans
    (subst (λ z → h * b + l < z) (mul-suc-gen b h) (+-mono-≤-< ≤-refl l<))
    (*-mono-≤ (suc-le b h h<) ≤-refl)

split-eq-gen : ∀ b {hx hy lx ly} → lx < b → ly < b →
  hx * b + lx ≡ hy * b + ly → (hx ≡ hy) × (lx ≡ ly)
split-eq-gen b {hx} {hy} {lx} {ly} lxb lyb eq with <-cmp hx hy
... | Tri.tri< hx<hy _ _ = ⊥-elim (<-irrefl eq (hi<→to64<-gen b lxb hx<hy))
... | Tri.tri> _ _ hx>hy = ⊥-elim (<-irrefl (sym eq) (hi<→to64<-gen b lyb hx>hy))
... | Tri.tri≈ _ hx≡hy _ = hx≡hy , +-cancelˡ-≡ (hx * b) lx ly
    (subst (λ z → hx * b + lx ≡ z * b + ly) (sym hx≡hy) eq)

lt→-gen : ∀ b {hx hy lx ly} → lx < b → ly < b → hx * b + lx < hy * b + ly →
  (hx < hy) ⊎ (hx ≡ hy × lx < ly)
lt→-gen b {hx} {hy} {lx} {ly} lxb lyb lt with <-cmp hx hy
... | Tri.tri< hx<hy _ _ = inj₁ hx<hy
... | Tri.tri> _ _ hx>hy = ⊥-elim (<-asym lt (hi<→to64<-gen b lyb hx>hy))
... | Tri.tri≈ _ hx≡hy _ = inj₂ (hx≡hy , +-cancelˡ-< (hx * b) lx ly
    (subst (λ z → hx * b + lx < z * b + ly) (sym hx≡hy) lt))

lt←-gen : ∀ b {hx hy lx ly} → lx < b →
  (hx < hy) ⊎ (hx ≡ hy × lx < ly) → hx * b + lx < hy * b + ly
lt←-gen b {hx} {hy} {lx} {ly} lxb (inj₁ hx<hy) = hi<→to64<-gen b lxb hx<hy
lt←-gen b {hx} {hy} {lx} {ly} lxb (inj₂ (hx≡hy , lx<ly)) =
  subst (λ z → hx * b + lx < z * b + ly) hx≡hy (+-mono-≤-< ≤-refl lx<ly)

le→-gen : ∀ b {hx hy lx ly} → lx < b → ly < b → hx * b + lx ≤ hy * b + ly →
  (hx < hy) ⊎ (hx ≡ hy × lx ≤ ly)
le→-gen b {hx} {hy} {lx} {ly} lxb lyb le with <-cmp hx hy
... | Tri.tri< hx<hy _ _ = inj₁ hx<hy
... | Tri.tri> _ _ hx>hy = ⊥-elim (<-irrefl refl (<-≤-trans (hi<→to64<-gen b lyb hx>hy) le))
... | Tri.tri≈ _ hx≡hy _ = inj₂ (hx≡hy , +-cancelˡ-≤ (hx * b) lx ly
    (subst (λ z → hx * b + lx ≤ z * b + ly) (sym hx≡hy) le))

le←-gen : ∀ b {hx hy lx ly} → lx < b →
  (hx < hy) ⊎ (hx ≡ hy × lx ≤ ly) → hx * b + lx ≤ hy * b + ly
le←-gen b {hx} {hy} {lx} {ly} lxb (inj₁ hx<hy) = <⇒≤ (hi<→to64<-gen b lxb hx<hy)
le←-gen b {hx} {hy} {lx} {ly} lxb (inj₂ (hx≡hy , lx≤ly)) =
  subst (λ z → hx * b + lx ≤ z * b + ly) hx≡hy (+-mono-≤ ≤-refl lx≤ly)


two32*two32≡two64 : two32 * two32 ≡ two64
two32*two32≡two64 = sym (^-distribˡ-+-* 2 32 32)

split-bound : ∀ h l → h < two32 → l < two32 → h * two32 + l < two64
split-bound h l h< l< =
  subst (λ z → h * two32 + l < z) two32*two32≡two64 (split-bound-gen two32 h l h< l<)

word32-eq : ∀ {x y : Word32} → to32 x ≡ to32 y → x ≡ y
word32-eq {x} {y} eq = Σ-≡,≡→≡ (eq , <-irrelevant _ _)

to64-eq-split : ∀ (x y : Word64) → to64 x ≡ to64 y →
  (to32 (proj₁ x) ≡ to32 (proj₁ y)) × (to32 (proj₂ x) ≡ to32 (proj₂ y))
to64-eq-split ((hx , _) , (lx , lxb)) ((hy , _) , (ly , lyb)) eq =
  split-eq-gen two32 lxb lyb eq

to64-inj : ∀ (x y : Word64) → to64 x ≡ to64 y → x ≡ y
to64-inj x y eq = cong₂ _,_ (word32-eq (proj₁ (to64-eq-split x y eq)))
                             (word32-eq (proj₂ (to64-eq-split x y eq)))

lt→ : ∀ (x y : Word64) → to64 x < to64 y →
  (to32 (proj₁ x) < to32 (proj₁ y)) ⊎
  ((to32 (proj₁ x) ≡ to32 (proj₁ y)) × (to32 (proj₂ x) < to32 (proj₂ y)))
lt→ ((hx , _) , (lx , lxb)) ((hy , _) , (ly , lyb)) lt = lt→-gen two32 lxb lyb lt

lt← : ∀ (x y : Word64) →
  (to32 (proj₁ x) < to32 (proj₁ y)) ⊎
  ((to32 (proj₁ x) ≡ to32 (proj₁ y)) × (to32 (proj₂ x) < to32 (proj₂ y))) →
  to64 x < to64 y
lt← ((hx , _) , (lx , lxb)) ((hy , _) , (ly , lyb)) d = lt←-gen two32 lxb d

le→ : ∀ (x y : Word64) → to64 x ≤ to64 y →
  (to32 (proj₁ x) < to32 (proj₁ y)) ⊎
  ((to32 (proj₁ x) ≡ to32 (proj₁ y)) × (to32 (proj₂ x) ≤ to32 (proj₂ y)))
le→ ((hx , _) , (lx , lxb)) ((hy , _) , (ly , lyb)) le = le→-gen two32 lxb lyb le

le← : ∀ (x y : Word64) →
  (to32 (proj₁ x) < to32 (proj₁ y)) ⊎
  ((to32 (proj₁ x) ≡ to32 (proj₁ y)) × (to32 (proj₂ x) ≤ to32 (proj₂ y))) →
  to64 x ≤ to64 y
le← ((hx , _) , (lx , lxb)) ((hy , _) , (ly , lyb)) d = le←-gen two32 lxb d
