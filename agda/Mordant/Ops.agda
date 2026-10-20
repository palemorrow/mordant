module Mordant.Ops where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≡ᵇ_; _<ᵇ_; _≤ᵇ_)
open import Data.Nat.Properties using
  (≡ᵇ⇒≡; ≡⇒≡ᵇ; <ᵇ⇒<; <⇒<ᵇ; ≤ᵇ⇒≤; ≤⇒≤ᵇ)
open import Data.Bool using (Bool; true; false; T; not; _∧_; _∨_; if_then_else_)
open import Data.Empty using (⊥-elim)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import Mordant.Word using (Word32; Word64; to32; to64; two32;
  lt→; lt←; le→; le←; to64-eq-split)

T∧→ : ∀ {a b : Bool} → T (a ∧ b) → T a × T b
T∧→ {true} {true} _ = _ , _
T∧→ {true} {false} ()
T∧→ {false} {_} ()

T∧← : ∀ {a b : Bool} → T a × T b → T (a ∧ b)
T∧← {true} {true} _ = _
T∧← {true} {false} (_ , ())
T∧← {false} {_} (() , _)

T∨→ : ∀ {a b : Bool} → T (a ∨ b) → T a ⊎ T b
T∨→ {true} _ = inj₁ _
T∨→ {false} {true} _ = inj₂ _
T∨→ {false} {false} ()

T∨← : ∀ {a b : Bool} → T a ⊎ T b → T (a ∨ b)
T∨← {true} _ = _
T∨← {false} {true} _ = _
T∨← {false} {false} (inj₁ ())
T∨← {false} {false} (inj₂ ())

bool-eq : ∀ {x y : Bool} → (T x → T y) → (T y → T x) → x ≡ y
bool-eq {true} {true} _ _ = refl
bool-eq {true} {false} f _ = ⊥-elim (f _)
bool-eq {false} {true} _ g = ⊥-elim (g _)
bool-eq {false} {false} _ _ = refl

T-of-true : ∀ (b : Bool) → b ≡ true → T b
T-of-true b e = subst (λ z → T z) (sym e) _

eq64-bool : ∀ (x y : Word64) →
  (to64 x ≡ᵇ to64 y) ≡
  ((to32 (proj₁ x) ≡ᵇ to32 (proj₁ y)) ∧ (to32 (proj₂ x) ≡ᵇ to32 (proj₂ y)))
eq64-bool x@((hx , hxb) , (lx , lxb)) y@((hy , hyb) , (ly , lyb)) = bool-eq fwd bwd
  where
  fwd : T (hx * two32 + lx ≡ᵇ hy * two32 + ly) → T ((hx ≡ᵇ hy) ∧ (lx ≡ᵇ ly))
  fwd t =
    T∧← ( ≡⇒≡ᵇ hx hy (proj₁ (to64-eq-split x y (≡ᵇ⇒≡ (hx * two32 + lx) (hy * two32 + ly) t)))
        , ≡⇒≡ᵇ lx ly (proj₂ (to64-eq-split x y (≡ᵇ⇒≡ (hx * two32 + lx) (hy * two32 + ly) t))) )
  bwd : T ((hx ≡ᵇ hy) ∧ (lx ≡ᵇ ly)) → T (hx * two32 + lx ≡ᵇ hy * two32 + ly)
  bwd t with T∧→ t
  ... | (h , l) =
    ≡⇒≡ᵇ (hx * two32 + lx) (hy * two32 + ly)
      (cong₂ (λ a b → a * two32 + b) (≡ᵇ⇒≡ hx hy h) (≡ᵇ⇒≡ lx ly l))

lt64-bool : ∀ (x y : Word64) →
  (to64 x <ᵇ to64 y) ≡
  ((to32 (proj₁ x) <ᵇ to32 (proj₁ y)) ∨
   ((to32 (proj₁ x) ≡ᵇ to32 (proj₁ y)) ∧ (to32 (proj₂ x) <ᵇ to32 (proj₂ y))))
lt64-bool x y = bool-eq fwd bwd
  where
  fwd : T (to64 x <ᵇ to64 y) → T ((to32 (proj₁ x) <ᵇ to32 (proj₁ y)) ∨
        ((to32 (proj₁ x) ≡ᵇ to32 (proj₁ y)) ∧ (to32 (proj₂ x) <ᵇ to32 (proj₂ y))))
  fwd t with lt→ x y (<ᵇ⇒< _ _ t)
  ... | inj₁ h = T∨← (inj₁ (<⇒<ᵇ h))
  ... | inj₂ (e , l) = T∨← (inj₂ (T∧← (≡⇒≡ᵇ _ _ e , <⇒<ᵇ l)))
  bwd : T ((to32 (proj₁ x) <ᵇ to32 (proj₁ y)) ∨
        ((to32 (proj₁ x) ≡ᵇ to32 (proj₁ y)) ∧ (to32 (proj₂ x) <ᵇ to32 (proj₂ y)))) →
        T (to64 x <ᵇ to64 y)
  bwd t with T∨→ t
  ... | inj₁ h = <⇒<ᵇ (lt← x y (inj₁ (<ᵇ⇒< _ _ h)))
  ... | inj₂ q with T∧→ q
  ... | (e , l) = <⇒<ᵇ (lt← x y (inj₂ (≡ᵇ⇒≡ _ _ e , <ᵇ⇒< _ _ l)))

le64-bool : ∀ (x y : Word64) →
  (to64 x ≤ᵇ to64 y) ≡
  ((to32 (proj₁ x) <ᵇ to32 (proj₁ y)) ∨
   ((to32 (proj₁ x) ≡ᵇ to32 (proj₁ y)) ∧ (to32 (proj₂ x) ≤ᵇ to32 (proj₂ y))))
le64-bool x y = bool-eq fwd bwd
  where
  fwd : T (to64 x ≤ᵇ to64 y) → T ((to32 (proj₁ x) <ᵇ to32 (proj₁ y)) ∨
        ((to32 (proj₁ x) ≡ᵇ to32 (proj₁ y)) ∧ (to32 (proj₂ x) ≤ᵇ to32 (proj₂ y))))
  fwd t with le→ x y (≤ᵇ⇒≤ _ _ t)
  ... | inj₁ h = T∨← (inj₁ (<⇒<ᵇ h))
  ... | inj₂ (e , l) = T∨← (inj₂ (T∧← (≡⇒≡ᵇ _ _ e , ≤⇒≤ᵇ l)))
  bwd : T ((to32 (proj₁ x) <ᵇ to32 (proj₁ y)) ∨
        ((to32 (proj₁ x) ≡ᵇ to32 (proj₁ y)) ∧ (to32 (proj₂ x) ≤ᵇ to32 (proj₂ y)))) →
        T (to64 x ≤ᵇ to64 y)
  bwd t with T∨→ t
  ... | inj₁ h = ≤⇒≤ᵇ (le← x y (inj₁ (<ᵇ⇒< _ _ h)))
  ... | inj₂ q with T∧→ q
  ... | (e , l) = ≤⇒≤ᵇ (le← x y (inj₂ (≡ᵇ⇒≡ _ _ e , ≤ᵇ⇒≤ _ _ l)))

if-∧ : ∀ {b1 b2 : Bool} (x y : ℕ) →
  (if b1 then (if b2 then x else y) else y) ≡ (if b1 ∧ b2 then x else y)
if-∧ {true} x y = refl
if-∧ {false} x y = refl

if-∨ : ∀ {b1 b2 : Bool} (x y : ℕ) →
  (if b1 then x else (if b2 then x else y)) ≡ (if b1 ∨ b2 then x else y)
if-∨ {true} x y = refl
if-∨ {false} x y = refl

if-not : ∀ {b : Bool} (x y : ℕ) → (if not b then x else y) ≡ (if b then y else x)
if-not {true} x y = refl
if-not {false} x y = refl
