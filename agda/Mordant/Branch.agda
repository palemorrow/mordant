module Mordant.Branch where

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤_)
open import Data.Nat using (_≡ᵇ_; _<ᵇ_; _≤ᵇ_)
open import Data.Nat.Properties using (m+[n∸m]≡n; +-identityʳ; +-suc)
open import Data.List using (List; []; _∷_; length)
open import Data.Maybe using (Maybe; just; nothing; maybe′)
open import Data.Maybe.Properties using (just-injective)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Unit using (⊤; tt)
open import Data.Product using (proj₁; proj₂; _×_; _,_)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)

open import Mordant.Word using (_&_)
open import Mordant.Semantics using (Env)
open import Mordant.BPF using (Instr; ldAbs; ldImm; andImm; jeq; jgt; jge; ja; ret;
  Program; run; runInstr; run-unfold; atInstr; loadWord; nothing≢just)

data AbsInstr : Set where
  aLdAbs : ℕ → AbsInstr
  aLdImm : ℕ → AbsInstr
  aAndImm : ℕ → AbsInstr
  aJeq : (k t f : ℕ) → AbsInstr
  aJgt : (k t f : ℕ) → AbsInstr
  aJge : (k t f : ℕ) → AbsInstr
  aJa : (t : ℕ) → AbsInstr
  aRet : (k : ℕ) → AbsInstr

AbsProgram : Set
AbsProgram = List AbsInstr

atAbs : AbsProgram → ℕ → Maybe AbsInstr
atAbs [] _ = nothing
atAbs (i ∷ _) zero = just i
atAbs (_ ∷ is) (suc n) = atAbs is n

mmap : ∀ {A B : Set} → (A → B) → Maybe A → Maybe B
mmap f (just x) = just (f x)
mmap f nothing = nothing

relative : ℕ → AbsInstr → Instr
relative pc (aLdAbs k) = ldAbs k
relative pc (aLdImm k) = ldImm k
relative pc (aAndImm k) = andImm k
relative pc (aJeq k t f) = jeq k (t ∸ suc pc) (f ∸ suc pc)
relative pc (aJgt k t f) = jgt k (t ∸ suc pc) (f ∸ suc pc)
relative pc (aJge k t f) = jge k (t ∸ suc pc) (f ∸ suc pc)
relative pc (aJa t) = ja (t ∸ suc pc)
relative pc (aRet k) = ret k

relativizeFrom : ℕ → AbsProgram → Program
relativizeFrom pc [] = []
relativizeFrom pc (i ∷ is) = relative pc i ∷ relativizeFrom (suc pc) is

relativize : AbsProgram → Program
relativize = relativizeFrom 0

relativizeFrom-length : ∀ pc xs → length (relativizeFrom pc xs) ≡ length xs
relativizeFrom-length pc [] = refl
relativizeFrom-length pc (i ∷ is) = cong suc (relativizeFrom-length (suc pc) is)

relativize-length : ∀ xs → length (relativize xs) ≡ length xs
relativize-length = relativizeFrom-length 0

atInstr-relativizeFrom : ∀ pc xs n →
  atInstr (relativizeFrom pc xs) n ≡ mmap (relative (pc + n)) (atAbs xs n)
atInstr-relativizeFrom pc [] n = refl
atInstr-relativizeFrom pc (i ∷ is) zero rewrite +-identityʳ pc = refl
atInstr-relativizeFrom pc (i ∷ is) (suc n) rewrite +-suc pc n =
  atInstr-relativizeFrom (suc pc) is n

atInstr-relativize : ∀ xs n →
  atInstr (relativize xs) n ≡ mmap (relative n) (atAbs xs n)
atInstr-relativize xs n = atInstr-relativizeFrom 0 xs n


tgtOK : ℕ → AbsInstr → Set
tgtOK pc (aJeq k t f) = (suc pc ≤ t) × (suc pc ≤ f)
tgtOK pc (aJgt k t f) = (suc pc ≤ t) × (suc pc ≤ f)
tgtOK pc (aJge k t f) = (suc pc ≤ t) × (suc pc ≤ f)
tgtOK pc (aJa t) = suc pc ≤ t
tgtOK pc _ = ⊤

Forward : AbsProgram → Set
Forward xs = ∀ pc i → atAbs xs pc ≡ just i → tgtOK pc i


mutual
  runAbs : AbsProgram → ℕ → ℕ → ℕ → ℕ → ℕ → Env → Maybe ℕ
  runAbs xs zero pc acc nr arch args = nothing
  runAbs xs (suc f) pc acc nr arch args =
    maybe′ (runInstrAbs xs f pc acc nr arch args) nothing (atAbs xs pc)

  runInstrAbs : AbsProgram → ℕ → ℕ → ℕ → ℕ → ℕ → Env → AbsInstr → Maybe ℕ
  runInstrAbs xs f pc acc nr arch args (aLdAbs k) =
    runAbs xs f (suc pc) (loadWord k nr arch args) nr arch args
  runInstrAbs xs f pc acc nr arch args (aLdImm k) = runAbs xs f (suc pc) k nr arch args
  runInstrAbs xs f pc acc nr arch args (aAndImm k) =
    runAbs xs f (suc pc) (acc & k) nr arch args
  runInstrAbs xs f pc acc nr arch args (aJeq k t fs) =
    runAbs xs f (if acc ≡ᵇ k then t else fs) acc nr arch args
  runInstrAbs xs f pc acc nr arch args (aJgt k t fs) =
    runAbs xs f (if k <ᵇ acc then t else fs) acc nr arch args
  runInstrAbs xs f pc acc nr arch args (aJge k t fs) =
    runAbs xs f (if k ≤ᵇ acc then t else fs) acc nr arch args
  runInstrAbs xs f pc acc nr arch args (aJa t) = runAbs xs f t acc nr arch args
  runInstrAbs xs f pc acc nr arch args (aRet k) = just k

relativize-run : ∀ xs → Forward xs → ∀ f pc acc nr arch args →
  run (relativize xs) f pc acc nr arch args ≡ runAbs xs f pc acc nr arch args
relativize-run xs fwd zero pc acc nr arch args = refl
relativize-run xs fwd (suc f) pc acc nr arch args =
  trans runL (trans main (sym runR))
  where
  gR = runInstr (relativize xs) f pc acc nr arch args
  gA = runInstrAbs xs f pc acc nr arch args

  runL : run (relativize xs) (suc f) pc acc nr arch args ≡
         maybe′ gR nothing (atInstr (relativize xs) pc)
  runL = refl

  runR : runAbs xs (suc f) pc acc nr arch args ≡
         maybe′ gA nothing (atAbs xs pc)
  runR = refl

  step-eq : ∀ (j : AbsInstr) → atAbs xs pc ≡ just j →
    runInstr (relativize xs) f pc acc nr arch args (relative pc j) ≡
    runInstrAbs xs f pc acc nr arch args j
  step-eq (aLdAbs k) e =
    relativize-run xs fwd f (suc pc) (loadWord k nr arch args) nr arch args
  step-eq (aLdImm k) e = relativize-run xs fwd f (suc pc) k nr arch args
  step-eq (aAndImm k) e = relativize-run xs fwd f (suc pc) (acc & k) nr arch args
  step-eq (aRet k) e = refl
  step-eq (aJa t) e =
    trans (cong (λ q → run (relativize xs) f q acc nr arch args)
                 (m+[n∸m]≡n (fwd pc (aJa t) e)))
          (relativize-run xs fwd f t acc nr arch args)
  step-eq (aJeq k t fs) e = bool-eq (acc ≡ᵇ k)
    where
    bool-eq : ∀ b →
      run (relativize xs) f (suc pc + (if b then (t ∸ suc pc) else (fs ∸ suc pc))) acc nr arch args ≡
      runAbs xs f (if b then t else fs) acc nr arch args
    bool-eq true =
      trans (cong (λ q → run (relativize xs) f q acc nr arch args)
                   (m+[n∸m]≡n (proj₁ (fwd pc (aJeq k t fs) e))))
            (relativize-run xs fwd f t acc nr arch args)
    bool-eq false =
      trans (cong (λ q → run (relativize xs) f q acc nr arch args)
                   (m+[n∸m]≡n (proj₂ (fwd pc (aJeq k t fs) e))))
            (relativize-run xs fwd f fs acc nr arch args)
  step-eq (aJgt k t fs) e = bool-eq (k <ᵇ acc)
    where
    bool-eq : ∀ b →
      run (relativize xs) f (suc pc + (if b then (t ∸ suc pc) else (fs ∸ suc pc))) acc nr arch args ≡
      runAbs xs f (if b then t else fs) acc nr arch args
    bool-eq true =
      trans (cong (λ q → run (relativize xs) f q acc nr arch args)
                   (m+[n∸m]≡n (proj₁ (fwd pc (aJgt k t fs) e))))
            (relativize-run xs fwd f t acc nr arch args)
    bool-eq false =
      trans (cong (λ q → run (relativize xs) f q acc nr arch args)
                   (m+[n∸m]≡n (proj₂ (fwd pc (aJgt k t fs) e))))
            (relativize-run xs fwd f fs acc nr arch args)
  step-eq (aJge k t fs) e = bool-eq (k ≤ᵇ acc)
    where
    bool-eq : ∀ b →
      run (relativize xs) f (suc pc + (if b then (t ∸ suc pc) else (fs ∸ suc pc))) acc nr arch args ≡
      runAbs xs f (if b then t else fs) acc nr arch args
    bool-eq true =
      trans (cong (λ q → run (relativize xs) f q acc nr arch args)
                   (m+[n∸m]≡n (proj₁ (fwd pc (aJge k t fs) e))))
            (relativize-run xs fwd f t acc nr arch args)
    bool-eq false =
      trans (cong (λ q → run (relativize xs) f q acc nr arch args)
                   (m+[n∸m]≡n (proj₂ (fwd pc (aJge k t fs) e))))
            (relativize-run xs fwd f fs acc nr arch args)
  main : maybe′ gR nothing (atInstr (relativize xs) pc) ≡
         maybe′ gA nothing (atAbs xs pc)
  main rewrite atInstr-relativize xs pc with atAbs xs pc in eq
  ... | nothing = refl
  ... | just i = step-eq i eq

