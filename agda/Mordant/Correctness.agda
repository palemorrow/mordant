{-# OPTIONS --rewriting #-}
module Mordant.Correctness where

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤_; _<_; s≤s; z≤n)
open import Data.Nat using (_≡ᵇ_; _<ᵇ_; _≤ᵇ_)
open import Data.Nat.Properties
  using (m≤m+n; m+[n∸m]≡n; ≤-refl; ≤-trans; +-mono-≤; +-suc; +-identityʳ; +-identityˡ;
         +-assoc; <⇒≤; <-irrefl; <-cmp; <-asym; ≤⇒≤ᵇ; ≤ᵇ⇒≤; <ᵇ⇒<; <⇒<ᵇ;
         ≮⇒≥; ≰⇒>; ≤-<-trans; ≡ᵇ⇒≡; ≡⇒≡ᵇ)
open import Data.Fin as F using (Fin)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (length-++; ++-assoc)
open import Data.Bool using (Bool; true; false; T; _∧_; _∨_; if_then_else_; not)
open import Data.Maybe using (Maybe; just; nothing; maybe′; fromMaybe)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; proj₁; proj₂; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary using (¬_)
open import Relation.Binary using (Tri)
open import Mordant.Ops using (T∧→; T∧←; T∨→; T∨←; bool-eq; eq64-bool; lt64-bool;
  le64-bool; if-∧; if-∨; if-not)

{-# BUILTIN REWRITE _≡_ #-}
{-# REWRITE +-suc #-}
{-# REWRITE +-identityʳ #-}


open import Mordant.Word using (Word64; to32; to64; w32; _&_;
  to64-eq-split; lt→; lt←; le→; le←)
open import Mordant.Policy
open import Mordant.Semantics using (Env; evalPred; evalRules; evalPolicy)
open import Mordant.BPF using (Instr; ret; Program; run; runProgram; nothing≢just; loadWord; load-lo; load-hi)
open import Mordant.Branch using (AbsInstr; aLdAbs; aLdImm; aAndImm; aJeq; aJgt;
  aJge; aJa; aRet; AbsProgram; atAbs; runAbs; runInstrAbs; relativize;
  relativize-length; relativize-run; Forward; tgtOK)
open import Mordant.Lower

record Conf : Set where
  constructor _,_
  field
    cpc : ℕ
    cacc : ℕ

open Conf

data Step (xs : AbsProgram) (nr arch : ℕ) (args : Env) : Conf → Conf → Set where
  sLdAbs : ∀ {pc a k} → atAbs xs pc ≡ just (aLdAbs k) →
    Step xs nr arch args (pc , a) (suc pc , loadWord k nr arch args)
  sLdImm : ∀ {pc a k} → atAbs xs pc ≡ just (aLdImm k) →
    Step xs nr arch args (pc , a) (suc pc , k)
  sAndImm : ∀ {pc a k} → atAbs xs pc ≡ just (aAndImm k) →
    Step xs nr arch args (pc , a) (suc pc , a & k)
  sJeq : ∀ {pc a k t f} → atAbs xs pc ≡ just (aJeq k t f) →
    Step xs nr arch args (pc , a) ((if a ≡ᵇ k then t else f) , a)
  sJgt : ∀ {pc a k t f} → atAbs xs pc ≡ just (aJgt k t f) →
    Step xs nr arch args (pc , a) ((if k <ᵇ a then t else f) , a)
  sJge : ∀ {pc a k t f} → atAbs xs pc ≡ just (aJge k t f) →
    Step xs nr arch args (pc , a) ((if k ≤ᵇ a then t else f) , a)
  sJa : ∀ {pc a t} → atAbs xs pc ≡ just (aJa t) →
    Step xs nr arch args (pc , a) (t , a)

data Reach (xs : AbsProgram) (nr arch : ℕ) (args : Env) : Conf → Conf → Set where
  refl : ∀ {c} → Reach xs nr arch args c c
  step : ∀ {c c' c''} → Step xs nr arch args c c' → Reach xs nr arch args c' c'' → Reach xs nr arch args c c''

steps : ∀ {xs nr arch args c c'} → Reach xs nr arch args c c' → ℕ
steps refl = 0
steps (step s p) = suc (steps p)

atAbs-++ : ∀ (pre rest : AbsProgram) n →
  atAbs (pre ++ rest) (length pre + n) ≡ atAbs rest n
atAbs-++ [] rest n = refl
atAbs-++ (x ∷ pre) rest n = atAbs-++ pre rest n

atAbs<length : ∀ {xs pc i} → atAbs xs pc ≡ just i → pc < length xs
atAbs<length {xs = []} ()
atAbs<length {xs = x ∷ xs} {pc = zero} e = s≤s z≤n
atAbs<length {xs = x ∷ xs} {pc = suc n} e = s≤s (atAbs<length {xs = xs} {pc = n} e)

step-fwd : ∀ {xs nr arch args c c'} → Forward xs → Step xs nr arch args c c' →
  suc (cpc c) ≤ cpc c'
step-fwd fwd (sLdAbs {pc} e) = ≤-refl
step-fwd fwd (sLdImm {pc} e) = ≤-refl
step-fwd fwd (sAndImm {pc} e) = ≤-refl
step-fwd {c = pc , a} fwd (sJeq {k = k} {t = t} {f = f} e) with a ≡ᵇ k
... | true = proj₁ (fwd pc (aJeq k t f) e)
... | false = proj₂ (fwd pc (aJeq k t f) e)
step-fwd {c = pc , a} fwd (sJgt {k = k} {t = t} {f = f} e) with k <ᵇ a
... | true = proj₁ (fwd pc (aJgt k t f) e)
... | false = proj₂ (fwd pc (aJgt k t f) e)
step-fwd {c = pc , a} fwd (sJge {k = k} {t = t} {f = f} e) with k ≤ᵇ a
... | true = proj₁ (fwd pc (aJge k t f) e)
... | false = proj₂ (fwd pc (aJge k t f) e)
step-fwd fwd (sJa {pc} {t = t} e) = fwd pc (aJa t) e

steps-le : ∀ {xs nr arch args c c'} → Forward xs → (p : Reach xs nr arch args c c') →
  cpc c + steps p ≤ cpc c'
steps-le {c = c} fwd refl = ≤-refl
steps-le {c = c} {c' = c'} fwd (step {c'' = c''} s p) =
  ≤-trans (+-mono-≤ (step-fwd fwd s) (≤-refl {x = steps p})) (steps-le fwd p)

step-run-eq : ∀ {xs nr arch args c c'} (s : Step xs nr arch args c c') (g : ℕ) →
  runAbs xs (suc g) (cpc c) (cacc c) nr arch args ≡
  runAbs xs g (cpc c') (cacc c') nr arch args
step-run-eq {xs} {nr} {arch} {args} (sLdAbs {pc} {a} e) g =
  trans (cong (maybe′ (runInstrAbs xs g pc a nr arch args) nothing) e) refl
step-run-eq {xs} {nr} {arch} {args} (sLdImm {pc} {a} e) g =
  trans (cong (maybe′ (runInstrAbs xs g pc a nr arch args) nothing) e) refl
step-run-eq {xs} {nr} {arch} {args} (sAndImm {pc} {a} e) g =
  trans (cong (maybe′ (runInstrAbs xs g pc a nr arch args) nothing) e) refl
step-run-eq {xs} {nr} {arch} {args} (sJeq {pc} {a} e) g =
  trans (cong (maybe′ (runInstrAbs xs g pc a nr arch args) nothing) e) refl
step-run-eq {xs} {nr} {arch} {args} (sJgt {pc} {a} e) g =
  trans (cong (maybe′ (runInstrAbs xs g pc a nr arch args) nothing) e) refl
step-run-eq {xs} {nr} {arch} {args} (sJge {pc} {a} e) g =
  trans (cong (maybe′ (runInstrAbs xs g pc a nr arch args) nothing) e) refl
step-run-eq {xs} {nr} {arch} {args} (sJa {pc} {a} e) g =
  trans (cong (maybe′ (runInstrAbs xs g pc a nr arch args) nothing) e) refl

reach-run : ∀ {xs nr arch args c c'} (p : Reach xs nr arch args c c') (g : ℕ) →
  runAbs xs (steps p + g) (cpc c) (cacc c) nr arch args ≡
  runAbs xs g (cpc c') (cacc c') nr arch args
reach-run refl g = refl
reach-run (step s p) g = trans (step-run-eq s (steps p + g)) (reach-run p g)

Reach-trans : ∀ {xs nr arch args c1 c2 c3} →
  Reach xs nr arch args c1 c2 → Reach xs nr arch args c2 c3 → Reach xs nr arch args c1 c3
Reach-trans refl q = q
Reach-trans (step s p) q = step s (Reach-trans p q)

runAbs-unfold : ∀ xs f pc acc nr arch args {i} → atAbs xs pc ≡ just i →
  runAbs xs (suc f) pc acc nr arch args ≡ runInstrAbs xs f pc acc nr arch args i
runAbs-unfold xs f pc acc nr arch args {i} eq =
  cong (maybe′ (runInstrAbs xs f pc acc nr arch args) nothing) eq

reach-ret : ∀ {xs nr arch args c pc acc} (pr : Reach xs nr arch args c (pc , acc)) X (g : ℕ) →
  atAbs xs pc ≡ just (aRet X) →
  runAbs xs (steps pr + suc g) (cpc c) (cacc c) nr arch args ≡ just X
reach-ret {xs} {nr} {arch} {args} pr X g e =
  trans (reach-run pr (suc g)) (runAbs-unfold xs g _ _ nr arch args e)

ForwardAt : ℕ → AbsProgram → Set
ForwardAt k xs = ∀ pc i → atAbs xs pc ≡ just i → tgtOK (k + pc) i

forwardAt-zero : ∀ xs → ForwardAt 0 xs → Forward xs
forwardAt-zero xs h pc i e = subst (λ z → tgtOK z i) (+-identityˡ pc) (h pc i e)

forwardAt-++ : ∀ k xs ys → ForwardAt k xs → ForwardAt (k + length xs) ys → ForwardAt k (xs ++ ys)
forwardAt-++ k [] ys hx hy = subst (λ z → ForwardAt z ys) (+-identityʳ k) hy
forwardAt-++ k (x ∷ xs) ys hx hy = go
  where
  hx' : ForwardAt (k + 1) xs
  hx' n i e = subst (λ z → tgtOK z i) (sym (+-assoc k 1 n)) (hx (suc n) i e)

  hy' : ForwardAt ((k + 1) + length xs) ys
  hy' = subst (λ z → ForwardAt z ys) (sym (+-assoc k 1 (length xs))) hy

  rec : ForwardAt (k + 1) (xs ++ ys)
  rec = forwardAt-++ (k + 1) xs ys hx' hy'

  go : ForwardAt k (x ∷ (xs ++ ys))
  go zero j e = subst (λ z → tgtOK (k + zero) z) (just-injective e)
                  (hx zero x refl)
  go (suc n) j e = subst (λ z → tgtOK z j) (+-assoc k 1 n) (rec n j e)

validBlock : ℕ → AbsProgram → Set
validBlock s [] = ⊤
validBlock s (i ∷ is) = tgtOK s i × validBlock (suc s) is

validBlock-++← : ∀ s xs ys → validBlock s xs → validBlock (s + length xs) ys → validBlock s (xs ++ ys)
validBlock-++← s [] ys vx vy = subst (λ z → validBlock z ys) (+-identityʳ s) vy
validBlock-++← s (x ∷ xs) ys (vx , vxs) vy =
  vx , validBlock-++← (suc s) xs ys vxs
         (subst (λ z → validBlock z ys) (+-suc s (length xs)) vy)

validBlock→ForwardAt : ∀ s B → validBlock s B → ForwardAt s B
validBlock→ForwardAt s [] v pc i e = ⊥-elim (nothing≢just e)
validBlock→ForwardAt s (i ∷ is) (v , vs) zero j e =
  subst (λ z → tgtOK (s + zero) z) (just-injective e)
    (subst (λ z → tgtOK z i) (sym (+-identityʳ s)) v)
validBlock→ForwardAt s (i ∷ is) (v , vs) (suc n) j e =
  subst (λ z → tgtOK z j) (sym (+-suc s n)) (validBlock→ForwardAt (suc s) is vs n j e)

validTestJeq : ∀ i k t f → i + 3 ≤ t → i + 5 ≤ f → validBlock i (testJeq i k t f)
validTestJeq i k t f h1 h2 =
  ( m≤m+n (suc i) 1 , m≤m+n (suc i) 3 )
  , _ , ( h1 , _ , ( h2 , _ ) )

validTestJgt : ∀ i k t f → i + 3 ≤ t → i + 5 ≤ f → validBlock i (testJgt i k t f)
validTestJgt i k t f h1 h2 =
  ( m≤m+n (suc i) 1 , m≤m+n (suc i) 3 )
  , _ , ( h1 , _ , ( h2 , _ ) )

validTestJge : ∀ i k t f → i + 3 ≤ t → i + 5 ≤ f → validBlock i (testJge i k t f)
validTestJge i k t f h1 h2 =
  ( m≤m+n (suc i) 1 , m≤m+n (suc i) 3 )
  , _ , ( h1 , _ , ( h2 , _ ) )

validRets : ∀ s X Y → validBlock s (aRet X ∷ aRet Y ∷ [])
validRets s X Y = _ , ( _ , _ )

validPred : ∀ s pr t f → s + size pr ≤ t → s + size pr ≤ f → validBlock s (compilePred s pr t f)
validPred s ptrue t f lt1 lt2 = _ , ( lt1 , _ )
validPred s (peq a c) t f lt1 lt2 =
  validBlock-++← s B1 B2
    ( _ , validTestJeq (s + 1) (to32 (proj₁ c)) (s + 6) f
            (m≤m+n (s + 4) 2)
            (≤-trans (m≤m+n (s + 6) 6) lt2) )
    ( _ , validTestJeq (s + 7) (to32 (proj₂ c)) t f
            (≤-trans (m≤m+n (s + 10) 2) (≤-trans (m≤m+n (s + 12) 0) lt1))
            lt2 )
  where
  B1 = aLdAbs (off a + 4) ∷ testJeq (s + 1) (to32 (proj₁ c)) (s + 6) f
  B2 = aLdAbs (off a) ∷ testJeq (s + 7) (to32 (proj₂ c)) t f
validPred s (pne a c) t f lt1 lt2 = validPred s (peq a c) f t lt2 lt1
validPred s (plt a c) t f lt1 lt2 =
  validBlock-++← s B1 (B2 ++ B3)
    ( _ , validTestJgt (s + 1) (to32 (proj₁ c)) f (s + 6)
            (≤-trans (m≤m+n (s + 4) 2) (≤-trans (m≤m+n (s + 6) 11) lt2))
            ≤-refl )
    ( validBlock-++← (s + 6) B2 B3
        ( validTestJeq (s + 6) (to32 (proj₁ c)) (s + 11) t
            (m≤m+n (s + 9) 2)
            (≤-trans (m≤m+n (s + 11) 6) lt1) )
        ( _ , validTestJge (s + 12) (to32 (proj₂ c)) f t
                (≤-trans (m≤m+n (s + 15) 2) lt2)
                (≤-trans (m≤m+n (s + 17) 0) lt1) ) )
  where
  B1 = aLdAbs (off a + 4) ∷ testJgt (s + 1) (to32 (proj₁ c)) f (s + 6)
  B2 = testJeq (s + 6) (to32 (proj₁ c)) (s + 11) t
  B3 = aLdAbs (off a) ∷ testJge (s + 12) (to32 (proj₂ c)) f t
validPred s (ple a c) t f lt1 lt2 =
  validBlock-++← s B1 (B2 ++ B3)
    ( _ , validTestJgt (s + 1) (to32 (proj₁ c)) f (s + 6)
            (≤-trans (m≤m+n (s + 4) 2) (≤-trans (m≤m+n (s + 6) 11) lt2))
            ≤-refl )
    ( validBlock-++← (s + 6) B2 B3
        ( validTestJeq (s + 6) (to32 (proj₁ c)) (s + 11) t
            (m≤m+n (s + 9) 2)
            (≤-trans (m≤m+n (s + 11) 6) lt1) )
        ( _ , validTestJgt (s + 12) (to32 (proj₂ c)) f t
                (≤-trans (m≤m+n (s + 15) 2) lt2)
                (≤-trans (m≤m+n (s + 17) 0) lt1) ) )
  where
  B1 = aLdAbs (off a + 4) ∷ testJgt (s + 1) (to32 (proj₁ c)) f (s + 6)
  B2 = testJeq (s + 6) (to32 (proj₁ c)) (s + 11) t
  B3 = aLdAbs (off a) ∷ testJgt (s + 12) (to32 (proj₂ c)) f t
validPred s (pgt a c) t f lt1 lt2 =
  validBlock-++← s B1 (B2 ++ B3)
    ( _ , validTestJgt (s + 1) (to32 (proj₁ c)) t (s + 6)
            (≤-trans (m≤m+n (s + 4) 2) (≤-trans (m≤m+n (s + 6) 11) lt1))
            ≤-refl )
    ( validBlock-++← (s + 6) B2 B3
        ( validTestJeq (s + 6) (to32 (proj₁ c)) (s + 11) f
            (m≤m+n (s + 9) 2)
            (≤-trans (m≤m+n (s + 11) 6) lt2) )
        ( _ , validTestJgt (s + 12) (to32 (proj₂ c)) t f
                (≤-trans (m≤m+n (s + 15) 2) lt1)
                (≤-trans (m≤m+n (s + 17) 0) lt2) ) )
  where
  B1 = aLdAbs (off a + 4) ∷ testJgt (s + 1) (to32 (proj₁ c)) t (s + 6)
  B2 = testJeq (s + 6) (to32 (proj₁ c)) (s + 11) f
  B3 = aLdAbs (off a) ∷ testJgt (s + 12) (to32 (proj₂ c)) t f
validPred s (pge a c) t f lt1 lt2 =
  validBlock-++← s B1 (B2 ++ B3)
    ( _ , validTestJgt (s + 1) (to32 (proj₁ c)) t (s + 6)
            (≤-trans (m≤m+n (s + 4) 2) (≤-trans (m≤m+n (s + 6) 11) lt1))
            ≤-refl )
    ( validBlock-++← (s + 6) B2 B3
        ( validTestJeq (s + 6) (to32 (proj₁ c)) (s + 11) f
            (m≤m+n (s + 9) 2)
            (≤-trans (m≤m+n (s + 11) 6) lt2) )
        ( _ , validTestJge (s + 12) (to32 (proj₂ c)) t f
                (≤-trans (m≤m+n (s + 15) 2) lt1)
                (≤-trans (m≤m+n (s + 17) 0) lt2) ) )
  where
  B1 = aLdAbs (off a + 4) ∷ testJgt (s + 1) (to32 (proj₁ c)) t (s + 6)
  B2 = testJeq (s + 6) (to32 (proj₁ c)) (s + 11) f
  B3 = aLdAbs (off a) ∷ testJge (s + 12) (to32 (proj₂ c)) t f
validPred s (pmaskzero a m) t f lt1 lt2 =
  validBlock-++← s B1 B2
    ( _ , ( _ , validTestJeq (s + 2) 0 (s + 7) f
            (m≤m+n (s + 5) 2)
            (≤-trans (m≤m+n (s + 7) 7) lt2) ) )
    ( _ , ( _ , validTestJeq (s + 9) 0 t f
            (≤-trans (m≤m+n (s + 12) 2) lt1)
            lt2 ) )
  where
  B1 = aLdAbs (off a) ∷ aAndImm (to32 (proj₂ m)) ∷ testJeq (s + 2) 0 (s + 7) f
  B2 = aLdAbs (off a + 4) ∷ aAndImm (to32 (proj₁ m)) ∷ testJeq (s + 9) 0 t f
validPred s (pmaskeq a m v) t f lt1 lt2 =
  validBlock-++← s B1 B2
    ( _ , ( _ , validTestJeq (s + 2) (to32 (proj₂ v)) (s + 7) f
            (m≤m+n (s + 5) 2)
            (≤-trans (m≤m+n (s + 7) 7) lt2) ) )
    ( _ , ( _ , validTestJeq (s + 9) (to32 (proj₁ v)) t f
            (≤-trans (m≤m+n (s + 12) 2) lt1)
            lt2 ) )
  where
  B1 = aLdAbs (off a) ∷ aAndImm (to32 (proj₂ m)) ∷ testJeq (s + 2) (to32 (proj₂ v)) (s + 7) f
  B2 = aLdAbs (off a + 4) ∷ aAndImm (to32 (proj₁ m)) ∷ testJeq (s + 9) (to32 (proj₁ v)) t f
validPred s (pand a b) t f lt1 lt2 =
  validBlock-++← s (compilePred s a (s + size a) f) (compilePred (s + size a) b t f)
    (validPred s a (s + size a) f
      ≤-refl
      (≤-trans (m≤m+n (s + size a) (size b))
        (subst (λ z → z ≤ f) (sym (+-assoc s (size a) (size b))) lt2)))
    (subst (λ z → validBlock z (compilePred (s + size a) b t f))
      (sym (cong (s +_) (compilePred-length s a (s + size a) f)))
      (validPred (s + size a) b t f
        (subst (λ z → z ≤ t) (sym (+-assoc s (size a) (size b))) lt1)
        (subst (λ z → z ≤ f) (sym (+-assoc s (size a) (size b))) lt2)))
validPred s (por a b) t f lt1 lt2 =
  validBlock-++← s (compilePred s a t (s + size a)) (compilePred (s + size a) b t f)
    (validPred s a t (s + size a)
      (≤-trans (m≤m+n (s + size a) (size b))
        (subst (λ z → z ≤ t) (sym (+-assoc s (size a) (size b))) lt1))
      ≤-refl)
    (subst (λ z → validBlock z (compilePred (s + size a) b t f))
      (sym (cong (s +_) (compilePred-length s a t (s + size a))))
      (validPred (s + size a) b t f
        (subst (λ z → z ≤ t) (sym (+-assoc s (size a) (size b))) lt1)
        (subst (λ z → z ≤ f) (sym (+-assoc s (size a) (size b))) lt2)))

validRule : ∀ p r → validBlock p (compileRule p r)
validRule p r =
  validBlock-++← p (aLdAbs 0 ∷ aJeq (to32 (w32 (Rule.ruleNr r))) (p + 2) (p + ruleSize r) ∷ [])
    (compilePred (p + 2) (Rule.rulePred r) (p + 2 + size (Rule.rulePred r)) (p + ruleSize r)
     ++ aRet (actionCode (Rule.ruleAct r)) ∷ [])
    ( _ , (( ≤-refl , +-mono-≤ ≤-refl (m≤m+n 2 (size (Rule.rulePred r) + 1))) , _) )
    (validBlock-++← (p + 2)
      (compilePred (p + 2) (Rule.rulePred r) (p + 2 + size (Rule.rulePred r)) (p + ruleSize r))
      (aRet (actionCode (Rule.ruleAct r)) ∷ [])
      (validPred (p + 2) (Rule.rulePred r) (p + 2 + size (Rule.rulePred r)) (p + ruleSize r)
        ≤-refl
        (≤-trans (m≤m+n (p + 2 + size (Rule.rulePred r)) 1) ≤-refl))
      (_ , _))

validRules : ∀ p rules → validBlock p (compileRules p rules)
validRules p [] = _
validRules p (r ∷ rs) =
  validBlock-++← p (compileRule p r) (compileRules (p + ruleSize r) rs)
    (validRule p r)
    (subst (λ z → validBlock z (compileRules (p + ruleSize r) rs))
      (sym (cong (p +_) (compileRule-length p r)))
      (validRules (p + ruleSize r) rs))

guardProg : ℕ → ℕ → AbsProgram
guardProg parm rs =
  aLdAbs 4 ∷ aJeq (to32 (w32 parm)) 2 (6 + rs)
  ∷ aLdAbs 0 ∷ aAndImm X32_BIT ∷ aJeq 0 5 (6 + rs) ∷ []

validGuard : ∀ parm rs → validBlock 0 (guardProg parm rs)
validGuard parm rs =
  _ , ( ( ≤-refl , ≤-trans (m≤m+n 2 4) (m≤m+n 6 rs) )
      , ( _ , ( _ , ( ( ≤-refl , ≤-trans (m≤m+n 5 1) (m≤m+n 6 rs) ) , _ ) ) ) )

validCompileAbs : ∀ parm def rules → validBlock 0 (compileAbs (policy parm def rules))
validCompileAbs parm def rules =
  validBlock-++← 0 (guardProg parm (rulesSize rules))
    (compileRules 5 rules ++ (aRet (actionCode def) ∷ aRet (actionCode actKillProcess) ∷ []))
    (validGuard parm (rulesSize rules))
    (validBlock-++← 5 (compileRules 5 rules)
      (aRet (actionCode def) ∷ aRet (actionCode actKillProcess) ∷ [])
      (validRules 5 rules)
      (validRets (5 + rulesSize rules) (actionCode def) (actionCode actKillProcess)))

forwardAbs : ∀ p → Forward (compileAbs p)
forwardAbs (policy parm def rules) =
  forwardAt-zero (compileAbs (policy parm def rules))
    (validBlock→ForwardAt 0 (compileAbs (policy parm def rules))
      (validCompileAbs parm def rules))

T-not : ∀ {b : Bool} → (T b → ⊥) → T (not b)
T-not {true} f = ⊥-elim (f _)
T-not {false} _ = _

T-not→ : ∀ {b : Bool} → T (not b) → T b → ⊥
T-not→ {true} ()
T-not→ {false} _ ()

≡ᵇ-sym : ∀ a b → (a ≡ᵇ b) ≡ (b ≡ᵇ a)
≡ᵇ-sym a b = bool-eq fwd bwd
  where
  fwd : T (a ≡ᵇ b) → T (b ≡ᵇ a)
  fwd t = ≡⇒≡ᵇ b a (sym (≡ᵇ⇒≡ a b t))
  bwd : T (b ≡ᵇ a) → T (a ≡ᵇ b)
  bwd t = ≡⇒≡ᵇ a b (sym (≡ᵇ⇒≡ b a t))

ltᵇ-eqᵇ-⊥ : ∀ a b → T (a <ᵇ b) → T (a ≡ᵇ b) → ⊥
ltᵇ-eqᵇ-⊥ a b h e =
  <-irrefl refl (subst (λ z → z < b) (≡ᵇ⇒≡ a b e) (<ᵇ⇒< a b h))

ltᵇ-not : ∀ a b → (b <ᵇ a) ≡ not ((a <ᵇ b) ∨ (a ≡ᵇ b))
ltᵇ-not a b = bool-eq fwd bwd
  where
  fwd : T (b <ᵇ a) → T (not ((a <ᵇ b) ∨ (a ≡ᵇ b)))
  fwd t = T-not (λ u → [ notab , noteq ] (T∨→ u))
    where
    ba : b < a
    ba = <ᵇ⇒< b a t
    notab : T (a <ᵇ b) → ⊥
    notab s = <-asym (<ᵇ⇒< a b s) ba
    noteq : T (a ≡ᵇ b) → ⊥
    noteq s = <-irrefl refl (subst (λ z → b < z) (≡ᵇ⇒≡ a b s) ba)
  bwd : T (not ((a <ᵇ b) ∨ (a ≡ᵇ b))) → T (b <ᵇ a)
  bwd t with <-cmp a b
  ... | Tri.tri< a<b _ _ = ⊥-elim (T-not→ t (T∨← (inj₁ (<⇒<ᵇ a<b))))
  ... | Tri.tri≈ _ a≡b _ = ⊥-elim (T-not→ t (T∨← (inj₂ (≡⇒≡ᵇ a b a≡b))))
  ... | Tri.tri> _ _ b<a = <⇒<ᵇ b<a

leᵇ-not : ∀ a b → (a ≤ᵇ b) ≡ not (b <ᵇ a)
leᵇ-not a b = bool-eq fwd bwd
  where
  fwd : T (a ≤ᵇ b) → T (not (b <ᵇ a))
  fwd t = T-not (λ s → <-irrefl refl (≤-<-trans (≤ᵇ⇒≤ a b t) (<ᵇ⇒< b a s)))
  bwd : T (not (b <ᵇ a)) → T (a ≤ᵇ b)
  bwd t = ≤⇒≤ᵇ (≮⇒≥ {b} {a} (λ s → T-not→ t (<⇒<ᵇ s)))

ltᵇ-not-le : ∀ a b → (b <ᵇ a) ≡ not (a ≤ᵇ b)
ltᵇ-not-le a b = bool-eq fwd bwd
  where
  fwd : T (b <ᵇ a) → T (not (a ≤ᵇ b))
  fwd t = T-not (λ s → <-irrefl refl (≤-<-trans (≤ᵇ⇒≤ a b s) (<ᵇ⇒< b a t)))
  bwd : T (not (a ≤ᵇ b)) → T (b <ᵇ a)
  bwd t = <⇒<ᵇ (≰⇒> {a} {b} (λ s → T-not→ t (≤⇒≤ᵇ s)))

shape-lt : ∀ (h e l : Bool) (t f : ℕ) → (T h → T e → ⊥) →
  (if not (h ∨ e) then f else (if e then (if not l then f else t) else t))
  ≡ (if (h ∨ (e ∧ l)) then t else f)
shape-lt true true l t f neq = ⊥-elim (neq _ _)
shape-lt true false l t f neq = refl
shape-lt false true true t f neq = refl
shape-lt false true false t f neq = refl
shape-lt false false l t f neq = refl

evalPredN : Pred → Env → ℕ → ℕ → ℕ
evalPredN ptrue args t f = t
evalPredN (peq a c) args t f = if b1 then (if b2 then t else f) else f
  where
  b1 = to32 (proj₁ (args a)) ≡ᵇ to32 (proj₁ c)
  b2 = to32 (proj₂ (args a)) ≡ᵇ to32 (proj₂ c)
evalPredN (pne a c) args t f = evalPredN (peq a c) args f t
evalPredN (plt a c) args t f = if ch then f else (if eh then (if cl then f else t) else t)
  where
  ch = to32 (proj₁ c) <ᵇ to32 (proj₁ (args a))
  eh = to32 (proj₁ (args a)) ≡ᵇ to32 (proj₁ c)
  cl = to32 (proj₂ c) ≤ᵇ to32 (proj₂ (args a))
evalPredN (ple a c) args t f = if ch then f else (if eh then (if cl then f else t) else t)
  where
  ch = to32 (proj₁ c) <ᵇ to32 (proj₁ (args a))
  eh = to32 (proj₁ (args a)) ≡ᵇ to32 (proj₁ c)
  cl = to32 (proj₂ c) <ᵇ to32 (proj₂ (args a))
evalPredN (pgt a c) args t f = if ch then t else (if eh then (if cl then t else f) else f)
  where
  ch = to32 (proj₁ c) <ᵇ to32 (proj₁ (args a))
  eh = to32 (proj₁ (args a)) ≡ᵇ to32 (proj₁ c)
  cl = to32 (proj₂ c) <ᵇ to32 (proj₂ (args a))
evalPredN (pge a c) args t f = if ch then t else (if eh then (if cl then t else f) else f)
  where
  ch = to32 (proj₁ c) <ᵇ to32 (proj₁ (args a))
  eh = to32 (proj₁ (args a)) ≡ᵇ to32 (proj₁ c)
  cl = to32 (proj₂ c) ≤ᵇ to32 (proj₂ (args a))
evalPredN (pmaskzero a m) args t f = if zl then (if zh then t else f) else f
  where
  zl = (to32 (proj₂ (args a)) & to32 (proj₂ m)) ≡ᵇ 0
  zh = (to32 (proj₁ (args a)) & to32 (proj₁ m)) ≡ᵇ 0
evalPredN (pmaskeq a m v) args t f = if el then (if eh then t else f) else f
  where
  el = (to32 (proj₂ (args a)) & to32 (proj₂ m)) ≡ᵇ to32 (proj₂ v)
  eh = (to32 (proj₁ (args a)) & to32 (proj₁ m)) ≡ᵇ to32 (proj₁ v)
evalPredN (pand a b) args t f = if evalPred a args then evalPredN b args t f else f
evalPredN (por a b) args t f = if evalPred a args then t else evalPredN b args t f

evalPredN-eq : ∀ pr args t f → evalPredN pr args t f ≡ (if evalPred pr args then t else f)
evalPredN-eq ptrue args t f = refl
evalPredN-eq (peq a c) args t f =
  trans (if-∧ {b1} {b2} t f)
    (cong (λ z → if z then t else f) (sym (eq64-bool (args a) c)))
  where
  b1 = to32 (proj₁ (args a)) ≡ᵇ to32 (proj₁ c)
  b2 = to32 (proj₂ (args a)) ≡ᵇ to32 (proj₂ c)
evalPredN-eq (pne a c) args t f =
  trans (evalPredN-eq (peq a c) args f t)
    (sym (if-not {evalPred (peq a c) args} t f))
evalPredN-eq (plt a c) args t f
  rewrite ltᵇ-not (to32 (proj₁ (args a))) (to32 (proj₁ c))
        | leᵇ-not (to32 (proj₂ c)) (to32 (proj₂ (args a)))
        | lt64-bool (args a) c =
  shape-lt (to32 (proj₁ (args a)) <ᵇ to32 (proj₁ c))
           (to32 (proj₁ (args a)) ≡ᵇ to32 (proj₁ c))
           (to32 (proj₂ (args a)) <ᵇ to32 (proj₂ c))
           t f (ltᵇ-eqᵇ-⊥ (to32 (proj₁ (args a))) (to32 (proj₁ c)))
evalPredN-eq (ple a c) args t f
  rewrite ltᵇ-not (to32 (proj₁ (args a))) (to32 (proj₁ c))
        | ltᵇ-not-le (to32 (proj₂ (args a))) (to32 (proj₂ c))
        | le64-bool (args a) c =
  shape-lt (to32 (proj₁ (args a)) <ᵇ to32 (proj₁ c))
           (to32 (proj₁ (args a)) ≡ᵇ to32 (proj₁ c))
           (to32 (proj₂ (args a)) ≤ᵇ to32 (proj₂ c))
           t f (ltᵇ-eqᵇ-⊥ (to32 (proj₁ (args a))) (to32 (proj₁ c)))
evalPredN-eq (pgt a c) args t f
  rewrite lt64-bool c (args a)
        | ≡ᵇ-sym (to32 (proj₁ (args a))) (to32 (proj₁ c)) =
  trans (cong (λ z → if (to32 (proj₁ c) <ᵇ to32 (proj₁ (args a))) then t else z)
               (if-∧ {(to32 (proj₁ c) ≡ᵇ to32 (proj₁ (args a)))} {(to32 (proj₂ c) <ᵇ to32 (proj₂ (args a)))} t f))
        (if-∨ {(to32 (proj₁ c) <ᵇ to32 (proj₁ (args a)))} {((to32 (proj₁ c) ≡ᵇ to32 (proj₁ (args a))) ∧ (to32 (proj₂ c) <ᵇ to32 (proj₂ (args a))))} t f)
evalPredN-eq (pge a c) args t f
  rewrite le64-bool c (args a)
        | ≡ᵇ-sym (to32 (proj₁ (args a))) (to32 (proj₁ c)) =
  trans (cong (λ z → if (to32 (proj₁ c) <ᵇ to32 (proj₁ (args a))) then t else z)
               (if-∧ {(to32 (proj₁ c) ≡ᵇ to32 (proj₁ (args a)))} {(to32 (proj₂ c) ≤ᵇ to32 (proj₂ (args a)))} t f))
        (if-∨ {(to32 (proj₁ c) <ᵇ to32 (proj₁ (args a)))} {((to32 (proj₁ c) ≡ᵇ to32 (proj₁ (args a))) ∧ (to32 (proj₂ c) ≤ᵇ to32 (proj₂ (args a))))} t f)
evalPredN-eq (pmaskzero a m) args t f =
  if-∧ {((to32 (proj₂ (args a)) & to32 (proj₂ m)) ≡ᵇ 0)}
       {((to32 (proj₁ (args a)) & to32 (proj₁ m)) ≡ᵇ 0)} t f
evalPredN-eq (pmaskeq a m v) args t f =
  if-∧ {((to32 (proj₂ (args a)) & to32 (proj₂ m)) ≡ᵇ to32 (proj₂ v))}
       {((to32 (proj₁ (args a)) & to32 (proj₁ m)) ≡ᵇ to32 (proj₁ v))} t f
evalPredN-eq (pand a b) args t f =
  trans (cong (λ z → if evalPred a args then z else f) (evalPredN-eq b args t f))
        (if-∧ {evalPred a args} {evalPred b args} t f)
evalPredN-eq (por a b) args t f =
  trans (cong (λ z → if evalPred a args then t else z) (evalPredN-eq b args t f))
        (if-∨ {evalPred a args} {evalPred b args} t f)

branchReach : ∀ {nr arch} {args : Env} {xs : AbsProgram} (b : Bool) (pT pF a : ℕ)
  (E : Bool → Conf) →
  Reach xs nr arch args (pT , a) (E true) →
  Reach xs nr arch args (pF , a) (E false) →
  Reach xs nr arch args ((if b then pT else pF) , a) (E b)
branchReach true pT pF a E rT rF = rT
branchReach false pT pF a E rT rF = rF

cpc-if : ∀ (b : Bool) (x y : Conf) → cpc (if b then x else y) ≡ (if b then cpc x else cpc y)
cpc-if true x y = refl
cpc-if false x y = refl

trampEval : ∀ {nr arch} {args : Env} (xs : AbsProgram) (β k T F acc : ℕ) →
  atAbs xs β ≡ just (aJeq k (β + 2) (β + 4)) →
  atAbs xs (β + 2) ≡ just (aJa T) →
  atAbs xs (β + 4) ≡ just (aJa F) →
  Reach xs nr arch args (β , acc) ((if acc ≡ᵇ k then T else F) , acc)
trampEval xs β k T F acc e0 e2 e4 =
  step (sJeq e0)
    (branchReach (acc ≡ᵇ k) (β + 2) (β + 4) acc (λ b → (if b then T else F) , acc)
       (step (sJa e2) refl) (step (sJa e4) refl))

trampEvalGt : ∀ {nr arch} {args : Env} (xs : AbsProgram) (β k T F acc : ℕ) →
  atAbs xs β ≡ just (aJgt k (β + 2) (β + 4)) →
  atAbs xs (β + 2) ≡ just (aJa T) →
  atAbs xs (β + 4) ≡ just (aJa F) →
  Reach xs nr arch args (β , acc) ((if k <ᵇ acc then T else F) , acc)
trampEvalGt xs β k T F acc e0 e2 e4 =
  step (sJgt e0)
    (branchReach (k <ᵇ acc) (β + 2) (β + 4) acc (λ b → (if b then T else F) , acc)
       (step (sJa e2) refl) (step (sJa e4) refl))

trampEvalGe : ∀ {nr arch} {args : Env} (xs : AbsProgram) (β k T F acc : ℕ) →
  atAbs xs β ≡ just (aJge k (β + 2) (β + 4)) →
  atAbs xs (β + 2) ≡ just (aJa T) →
  atAbs xs (β + 4) ≡ just (aJa F) →
  Reach xs nr arch args (β , acc) ((if k ≤ᵇ acc then T else F) , acc)
trampEvalGe xs β k T F acc e0 e2 e4 =
  step (sJge e0)
    (branchReach (k ≤ᵇ acc) (β + 2) (β + 4) acc (λ b → (if b then T else F) , acc)
       (step (sJa e2) refl) (step (sJa e4) refl))

trampJoin : ∀ {nr arch} {args : Env} {xs : AbsProgram} {c : Conf} (b : Bool)
  (T F a : ℕ) (E : Bool → Conf) →
  Reach xs nr arch args c ((if b then T else F) , a) →
  Reach xs nr arch args (T , a) (E true) →
  Reach xs nr arch args (F , a) (E false) →
  Reach xs nr arch args c (E b)
trampJoin true T F a E r rT rF = Reach-trans r rT
trampJoin false T F a E r rT rF = Reach-trans r rF

endJoin : ∀ {nr arch} {args : Env} {xs : AbsProgram} {c : Conf} (b : Bool)
  (pT pF a : ℕ) (E : Bool → Conf) →
  Reach xs nr arch args c ((if b then pT else pF) , a) →
  Reach xs nr arch args (pT , a) (E true) →
  Reach xs nr arch args (pF , a) (E false) →
  Reach xs nr arch args c (E b)
endJoin true pT pF a E r rT rF = Reach-trans r rT
endJoin false pT pF a E r rT rF = Reach-trans r rF

pred-lemma : ∀ (pre rest : AbsProgram) (pr : Pred) (t f acc : ℕ) (nr arch : ℕ) (args : Env) →
  Σ Conf (λ c → Reach (pre ++ (compilePred (length pre) pr t f ++ rest)) nr arch args (length pre , acc) c
        × (cpc c ≡ (if evalPred pr args then t else f)))
pred-lemma pre rest ptrue t f acc nr arch args = (t , 0) , chain , refl
  where
  p = length pre
  R = compilePred p ptrue t f ++ rest
  P = pre ++ R
  H : ∀ j instr → atAbs R j ≡ just instr → atAbs P (p + j) ≡ just instr
  H j instr e = trans (atAbs-++ pre R j) e
  chain : Reach P nr arch args (p , acc) (t , 0)
  chain = step (sLdImm (H 0 (aLdImm 0) refl)) (step (sJa (H 1 (aJa t) refl)) refl)
pred-lemma pre rest (peq a c) t f acc nr arch args =
  E b1 , chain , evalPredN-eq (peq a c) args t f
  where
  p = length pre
  R = compilePred p (peq a c) t f ++ rest
  P = pre ++ R
  cHi = to32 (proj₁ c)
  cLo = to32 (proj₂ c)
  aHi = to32 (proj₁ (args a))
  aLo = to32 (proj₂ (args a))
  b1 = aHi ≡ᵇ cHi
  b2 = aLo ≡ᵇ cLo
  acc1 = loadWord (off a + 4) nr arch args
  acc0 = loadWord (off a) nr arch args
  H : ∀ j instr → atAbs R j ≡ just instr → atAbs P (p + j) ≡ just instr
  H j instr e = trans (atAbs-++ pre R j) e
  step1 : Reach P nr arch args (p , acc) (p + 1 , acc1)
  step1 = step (sLdAbs (H 0 (aLdAbs (off a + 4)) refl)) refl
  tramp1 : Reach P nr arch args (p + 1 , acc1) ((if acc1 ≡ᵇ cHi then p + 6 else f) , acc1)
  tramp1 = trampEval P (p + 1) cHi (p + 6) f acc1
             (H 1 (aJeq cHi (p + 3) (p + 5)) refl)
             (H 3 (aJa (p + 6)) refl)
             (H 5 (aJa f) refl)
  tramp1' : Reach P nr arch args (p + 1 , aHi) ((if b1 then p + 6 else f) , aHi)
  tramp1' = subst (λ z → Reach P nr arch args (p + 1 , z) ((if z ≡ᵇ cHi then p + 6 else f) , z))
                  (load-hi a nr arch args) tramp1
  step2 : Reach P nr arch args (p + 6 , aHi) (p + 7 , acc0)
  step2 = step (sLdAbs (H 6 (aLdAbs (off a)) refl)) refl
  tramp2 : Reach P nr arch args (p + 7 , acc0) ((if acc0 ≡ᵇ cLo then t else f) , acc0)
  tramp2 = trampEval P (p + 7) cLo t f acc0
             (H 7 (aJeq cLo (p + 9) (p + 11)) refl)
             (H 9 (aJa t) refl)
             (H 11 (aJa f) refl)
  rT : Reach P nr arch args (p + 6 , aHi) ((if b2 then t else f) , aLo)
  rT = subst (λ z → Reach P nr arch args (p + 6 , aHi) ((if z ≡ᵇ cLo then t else f) , z))
             (load-lo a nr arch args) (Reach-trans step2 tramp2)
  E : Bool → Conf
  E b = (if b then (if b2 then t else f) else f) , (if b then aLo else aHi)
  joined : Reach P nr arch args (p + 1 , aHi) (E b1)
  joined = trampJoin b1 (p + 6) f aHi E tramp1' rT refl
  chain : Reach P nr arch args (p , acc) (E b1)
  chain = Reach-trans
            (subst (λ z → Reach P nr arch args (p , acc) (p + 1 , z))
                   (load-hi a nr arch args) step1)
            joined
pred-lemma pre rest (pne a c) t f acc nr arch args
  with pred-lemma pre rest (peq a c) f t acc nr arch args
... | cc , r , e = cc , r , trans e (sym (if-not {evalPred (peq a c) args} t f))
pred-lemma pre rest (plt a c) t f acc nr arch args =
  E1 ch , chain , trans (cpc-if ch (f , aHi) (E2 eh)) (evalPredN-eq (plt a c) args t f)
  where
  p = length pre
  R = compilePred p (plt a c) t f ++ rest
  P = pre ++ R
  cHi = to32 (proj₁ c)
  cLo = to32 (proj₂ c)
  aHi = to32 (proj₁ (args a))
  aLo = to32 (proj₂ (args a))
  ch = cHi <ᵇ aHi
  eh = aHi ≡ᵇ cHi
  cl = cLo ≤ᵇ aLo
  acc1 = loadWord (off a + 4) nr arch args
  acc0 = loadWord (off a) nr arch args
  H : ∀ j instr → atAbs R j ≡ just instr → atAbs P (p + j) ≡ just instr
  H j instr e = trans (atAbs-++ pre R j) e
  step1 : Reach P nr arch args (p , acc) (p + 1 , acc1)
  step1 = step (sLdAbs (H 0 (aLdAbs (off a + 4)) refl)) refl
  tramp1 : Reach P nr arch args (p + 1 , acc1) ((if cHi <ᵇ acc1 then f else p + 6) , acc1)
  tramp1 = trampEvalGt P (p + 1) cHi f (p + 6) acc1
             (H 1 (aJgt cHi (p + 3) (p + 5)) refl)
             (H 3 (aJa f) refl)
             (H 5 (aJa (p + 6)) refl)
  tramp1' : Reach P nr arch args (p + 1 , aHi) ((if ch then f else p + 6) , aHi)
  tramp1' = subst (λ z → Reach P nr arch args (p + 1 , z) ((if cHi <ᵇ z then f else p + 6) , z))
                  (load-hi a nr arch args) tramp1
  tramp2 : Reach P nr arch args (p + 6 , aHi) ((if eh then p + 11 else t) , aHi)
  tramp2 = trampEval P (p + 6) cHi (p + 11) t aHi
             (H 6 (aJeq cHi (p + 8) (p + 10)) refl)
             (H 8 (aJa (p + 11)) refl)
             (H 10 (aJa t) refl)
  step11 : Reach P nr arch args (p + 11 , aHi) (p + 12 , acc0)
  step11 = step (sLdAbs (H 11 (aLdAbs (off a)) refl)) refl
  tramp3 : Reach P nr arch args (p + 12 , acc0) ((if cLo ≤ᵇ acc0 then f else t) , acc0)
  tramp3 = trampEvalGe P (p + 12) cLo f t acc0
             (H 12 (aJge cLo (p + 14) (p + 16)) refl)
             (H 14 (aJa f) refl)
             (H 16 (aJa t) refl)
  from11 : Reach P nr arch args (p + 11 , aHi) ((if cl then f else t) , aLo)
  from11 = subst (λ z → Reach P nr arch args (p + 11 , aHi) ((if cLo ≤ᵇ z then f else t) , z))
                 (load-lo a nr arch args) (Reach-trans step11 tramp3)
  E2 : Bool → Conf
  E2 b = (if b then (if cl then f else t) else t) , (if b then aLo else aHi)
  r6 : Reach P nr arch args (p + 6 , aHi) (E2 eh)
  r6 = trampJoin eh (p + 11) t aHi E2 tramp2 from11 refl
  E1 : Bool → Conf
  E1 b = if b then (f , aHi) else E2 eh
  joined : Reach P nr arch args (p + 1 , aHi) (E1 ch)
  joined = trampJoin ch f (p + 6) aHi E1 tramp1' refl r6
  chain : Reach P nr arch args (p , acc) (E1 ch)
  chain = Reach-trans
            (subst (λ z → Reach P nr arch args (p , acc) (p + 1 , z))
                   (load-hi a nr arch args) step1)
            joined
pred-lemma pre rest (ple a c) t f acc nr arch args =
  E1 ch , chain , trans (cpc-if ch (f , aHi) (E2 eh)) (evalPredN-eq (ple a c) args t f)
  where
  p = length pre
  R = compilePred p (ple a c) t f ++ rest
  P = pre ++ R
  cHi = to32 (proj₁ c)
  cLo = to32 (proj₂ c)
  aHi = to32 (proj₁ (args a))
  aLo = to32 (proj₂ (args a))
  ch = cHi <ᵇ aHi
  eh = aHi ≡ᵇ cHi
  cl = cLo <ᵇ aLo
  acc1 = loadWord (off a + 4) nr arch args
  acc0 = loadWord (off a) nr arch args
  H : ∀ j instr → atAbs R j ≡ just instr → atAbs P (p + j) ≡ just instr
  H j instr e = trans (atAbs-++ pre R j) e
  step1 : Reach P nr arch args (p , acc) (p + 1 , acc1)
  step1 = step (sLdAbs (H 0 (aLdAbs (off a + 4)) refl)) refl
  tramp1 : Reach P nr arch args (p + 1 , acc1) ((if cHi <ᵇ acc1 then f else p + 6) , acc1)
  tramp1 = trampEvalGt P (p + 1) cHi f (p + 6) acc1
             (H 1 (aJgt cHi (p + 3) (p + 5)) refl)
             (H 3 (aJa f) refl)
             (H 5 (aJa (p + 6)) refl)
  tramp1' : Reach P nr arch args (p + 1 , aHi) ((if ch then f else p + 6) , aHi)
  tramp1' = subst (λ z → Reach P nr arch args (p + 1 , z) ((if cHi <ᵇ z then f else p + 6) , z))
                  (load-hi a nr arch args) tramp1
  tramp2 : Reach P nr arch args (p + 6 , aHi) ((if eh then p + 11 else t) , aHi)
  tramp2 = trampEval P (p + 6) cHi (p + 11) t aHi
             (H 6 (aJeq cHi (p + 8) (p + 10)) refl)
             (H 8 (aJa (p + 11)) refl)
             (H 10 (aJa t) refl)
  step11 : Reach P nr arch args (p + 11 , aHi) (p + 12 , acc0)
  step11 = step (sLdAbs (H 11 (aLdAbs (off a)) refl)) refl
  tramp3 : Reach P nr arch args (p + 12 , acc0) ((if cLo <ᵇ acc0 then f else t) , acc0)
  tramp3 = trampEvalGt P (p + 12) cLo f t acc0
             (H 12 (aJgt cLo (p + 14) (p + 16)) refl)
             (H 14 (aJa f) refl)
             (H 16 (aJa t) refl)
  from11 : Reach P nr arch args (p + 11 , aHi) ((if cl then f else t) , aLo)
  from11 = subst (λ z → Reach P nr arch args (p + 11 , aHi) ((if cLo <ᵇ z then f else t) , z))
                 (load-lo a nr arch args) (Reach-trans step11 tramp3)
  E2 : Bool → Conf
  E2 b = (if b then (if cl then f else t) else t) , (if b then aLo else aHi)
  r6 : Reach P nr arch args (p + 6 , aHi) (E2 eh)
  r6 = trampJoin eh (p + 11) t aHi E2 tramp2 from11 refl
  E1 : Bool → Conf
  E1 b = if b then (f , aHi) else E2 eh
  joined : Reach P nr arch args (p + 1 , aHi) (E1 ch)
  joined = trampJoin ch f (p + 6) aHi E1 tramp1' refl r6
  chain : Reach P nr arch args (p , acc) (E1 ch)
  chain = Reach-trans
            (subst (λ z → Reach P nr arch args (p , acc) (p + 1 , z))
                   (load-hi a nr arch args) step1)
            joined
pred-lemma pre rest (pgt a c) t f acc nr arch args =
  E1 ch , chain , trans (cpc-if ch (t , aHi) (E2 eh)) (evalPredN-eq (pgt a c) args t f)
  where
  p = length pre
  R = compilePred p (pgt a c) t f ++ rest
  P = pre ++ R
  cHi = to32 (proj₁ c)
  cLo = to32 (proj₂ c)
  aHi = to32 (proj₁ (args a))
  aLo = to32 (proj₂ (args a))
  ch = cHi <ᵇ aHi
  eh = aHi ≡ᵇ cHi
  cl = cLo <ᵇ aLo
  acc1 = loadWord (off a + 4) nr arch args
  acc0 = loadWord (off a) nr arch args
  H : ∀ j instr → atAbs R j ≡ just instr → atAbs P (p + j) ≡ just instr
  H j instr e = trans (atAbs-++ pre R j) e
  step1 : Reach P nr arch args (p , acc) (p + 1 , acc1)
  step1 = step (sLdAbs (H 0 (aLdAbs (off a + 4)) refl)) refl
  tramp1 : Reach P nr arch args (p + 1 , acc1) ((if cHi <ᵇ acc1 then t else p + 6) , acc1)
  tramp1 = trampEvalGt P (p + 1) cHi t (p + 6) acc1
             (H 1 (aJgt cHi (p + 3) (p + 5)) refl)
             (H 3 (aJa t) refl)
             (H 5 (aJa (p + 6)) refl)
  tramp1' : Reach P nr arch args (p + 1 , aHi) ((if ch then t else p + 6) , aHi)
  tramp1' = subst (λ z → Reach P nr arch args (p + 1 , z) ((if cHi <ᵇ z then t else p + 6) , z))
                  (load-hi a nr arch args) tramp1
  tramp2 : Reach P nr arch args (p + 6 , aHi) ((if eh then p + 11 else f) , aHi)
  tramp2 = trampEval P (p + 6) cHi (p + 11) f aHi
             (H 6 (aJeq cHi (p + 8) (p + 10)) refl)
             (H 8 (aJa (p + 11)) refl)
             (H 10 (aJa f) refl)
  step11 : Reach P nr arch args (p + 11 , aHi) (p + 12 , acc0)
  step11 = step (sLdAbs (H 11 (aLdAbs (off a)) refl)) refl
  tramp3 : Reach P nr arch args (p + 12 , acc0) ((if cLo <ᵇ acc0 then t else f) , acc0)
  tramp3 = trampEvalGt P (p + 12) cLo t f acc0
             (H 12 (aJgt cLo (p + 14) (p + 16)) refl)
             (H 14 (aJa t) refl)
             (H 16 (aJa f) refl)
  from11 : Reach P nr arch args (p + 11 , aHi) ((if cl then t else f) , aLo)
  from11 = subst (λ z → Reach P nr arch args (p + 11 , aHi) ((if cLo <ᵇ z then t else f) , z))
                 (load-lo a nr arch args) (Reach-trans step11 tramp3)
  E2 : Bool → Conf
  E2 b = (if b then (if cl then t else f) else f) , (if b then aLo else aHi)
  r6 : Reach P nr arch args (p + 6 , aHi) (E2 eh)
  r6 = trampJoin eh (p + 11) f aHi E2 tramp2 from11 refl
  E1 : Bool → Conf
  E1 b = if b then (t , aHi) else E2 eh
  joined : Reach P nr arch args (p + 1 , aHi) (E1 ch)
  joined = trampJoin ch t (p + 6) aHi E1 tramp1' refl r6
  chain : Reach P nr arch args (p , acc) (E1 ch)
  chain = Reach-trans
            (subst (λ z → Reach P nr arch args (p , acc) (p + 1 , z))
                   (load-hi a nr arch args) step1)
            joined
pred-lemma pre rest (pge a c) t f acc nr arch args =
  E1 ch , chain , trans (cpc-if ch (t , aHi) (E2 eh)) (evalPredN-eq (pge a c) args t f)
  where
  p = length pre
  R = compilePred p (pge a c) t f ++ rest
  P = pre ++ R
  cHi = to32 (proj₁ c)
  cLo = to32 (proj₂ c)
  aHi = to32 (proj₁ (args a))
  aLo = to32 (proj₂ (args a))
  ch = cHi <ᵇ aHi
  eh = aHi ≡ᵇ cHi
  cl = cLo ≤ᵇ aLo
  acc1 = loadWord (off a + 4) nr arch args
  acc0 = loadWord (off a) nr arch args
  H : ∀ j instr → atAbs R j ≡ just instr → atAbs P (p + j) ≡ just instr
  H j instr e = trans (atAbs-++ pre R j) e
  step1 : Reach P nr arch args (p , acc) (p + 1 , acc1)
  step1 = step (sLdAbs (H 0 (aLdAbs (off a + 4)) refl)) refl
  tramp1 : Reach P nr arch args (p + 1 , acc1) ((if cHi <ᵇ acc1 then t else p + 6) , acc1)
  tramp1 = trampEvalGt P (p + 1) cHi t (p + 6) acc1
             (H 1 (aJgt cHi (p + 3) (p + 5)) refl)
             (H 3 (aJa t) refl)
             (H 5 (aJa (p + 6)) refl)
  tramp1' : Reach P nr arch args (p + 1 , aHi) ((if ch then t else p + 6) , aHi)
  tramp1' = subst (λ z → Reach P nr arch args (p + 1 , z) ((if cHi <ᵇ z then t else p + 6) , z))
                  (load-hi a nr arch args) tramp1
  tramp2 : Reach P nr arch args (p + 6 , aHi) ((if eh then p + 11 else f) , aHi)
  tramp2 = trampEval P (p + 6) cHi (p + 11) f aHi
             (H 6 (aJeq cHi (p + 8) (p + 10)) refl)
             (H 8 (aJa (p + 11)) refl)
             (H 10 (aJa f) refl)
  step11 : Reach P nr arch args (p + 11 , aHi) (p + 12 , acc0)
  step11 = step (sLdAbs (H 11 (aLdAbs (off a)) refl)) refl
  tramp3 : Reach P nr arch args (p + 12 , acc0) ((if cLo ≤ᵇ acc0 then t else f) , acc0)
  tramp3 = trampEvalGe P (p + 12) cLo t f acc0
             (H 12 (aJge cLo (p + 14) (p + 16)) refl)
             (H 14 (aJa t) refl)
             (H 16 (aJa f) refl)
  from11 : Reach P nr arch args (p + 11 , aHi) ((if cl then t else f) , aLo)
  from11 = subst (λ z → Reach P nr arch args (p + 11 , aHi) ((if cLo ≤ᵇ z then t else f) , z))
                 (load-lo a nr arch args) (Reach-trans step11 tramp3)
  E2 : Bool → Conf
  E2 b = (if b then (if cl then t else f) else f) , (if b then aLo else aHi)
  r6 : Reach P nr arch args (p + 6 , aHi) (E2 eh)
  r6 = trampJoin eh (p + 11) f aHi E2 tramp2 from11 refl
  E1 : Bool → Conf
  E1 b = if b then (t , aHi) else E2 eh
  joined : Reach P nr arch args (p + 1 , aHi) (E1 ch)
  joined = trampJoin ch t (p + 6) aHi E1 tramp1' refl r6
  chain : Reach P nr arch args (p , acc) (E1 ch)
  chain = Reach-trans
            (subst (λ z → Reach P nr arch args (p , acc) (p + 1 , z))
                   (load-hi a nr arch args) step1)
            joined
pred-lemma pre rest (pmaskzero a m) t f acc nr arch args =
  E1 zl , chain , trans (cpc-if zl (E2 zh) (f , aLo & to32 (proj₂ m))) (evalPredN-eq (pmaskzero a m) args t f)
  where
  p = length pre
  R = compilePred p (pmaskzero a m) t f ++ rest
  P = pre ++ R
  aHi = to32 (proj₁ (args a))
  aLo = to32 (proj₂ (args a))
  zl = (aLo & to32 (proj₂ m)) ≡ᵇ 0
  zh = (aHi & to32 (proj₁ m)) ≡ᵇ 0
  H : ∀ j instr → atAbs R j ≡ just instr → atAbs P (p + j) ≡ just instr
  H j instr e = trans (atAbs-++ pre R j) e
  step0 : Reach P nr arch args (p , acc) (p + 1 , aLo)
  step0 = subst (λ z → Reach P nr arch args (p , acc) (p + 1 , z))
               (load-lo a nr arch args) (step (sLdAbs (H 0 (aLdAbs (off a)) refl)) refl)
  step1 : Reach P nr arch args (p + 1 , aLo) (p + 2 , aLo & to32 (proj₂ m))
  step1 = step (sAndImm (H 1 (aAndImm (to32 (proj₂ m))) refl)) refl
  tramp1 : Reach P nr arch args (p + 2 , aLo & to32 (proj₂ m))
             ((if (aLo & to32 (proj₂ m)) ≡ᵇ 0 then p + 7 else f) , aLo & to32 (proj₂ m))
  tramp1 = trampEval P (p + 2) 0 (p + 7) f (aLo & to32 (proj₂ m))
             (H 2 (aJeq 0 (p + 4) (p + 6)) refl)
             (H 4 (aJa (p + 7)) refl)
             (H 6 (aJa f) refl)
  step7 : Reach P nr arch args (p + 7 , aLo & to32 (proj₂ m)) (p + 8 , aHi)
  step7 = subst (λ z → Reach P nr arch args (p + 7 , aLo & to32 (proj₂ m)) (p + 8 , z))
               (load-hi a nr arch args) (step (sLdAbs (H 7 (aLdAbs (off a + 4)) refl)) refl)
  step8 : Reach P nr arch args (p + 8 , aHi) (p + 9 , aHi & to32 (proj₁ m))
  step8 = step (sAndImm (H 8 (aAndImm (to32 (proj₁ m))) refl)) refl
  tramp2 : Reach P nr arch args (p + 9 , aHi & to32 (proj₁ m))
             ((if (aHi & to32 (proj₁ m)) ≡ᵇ 0 then t else f) , aHi & to32 (proj₁ m))
  tramp2 = trampEval P (p + 9) 0 t f (aHi & to32 (proj₁ m))
             (H 9 (aJeq 0 (p + 11) (p + 13)) refl)
             (H 11 (aJa t) refl)
             (H 13 (aJa f) refl)
  from7 : Reach P nr arch args (p + 7 , aLo & to32 (proj₂ m))
            ((if zh then t else f) , aHi & to32 (proj₁ m))
  from7 = Reach-trans step7 (Reach-trans step8 tramp2)
  E2 : Bool → Conf
  E2 b = (if b then t else f) , (aHi & to32 (proj₁ m))
  rT : Reach P nr arch args (p + 7 , aLo & to32 (proj₂ m)) (E2 zh)
  rT = from7
  E1 : Bool → Conf
  E1 b = if b then E2 zh else (f , aLo & to32 (proj₂ m))
  joined : Reach P nr arch args (p + 2 , aLo & to32 (proj₂ m)) (E1 zl)
  joined = trampJoin zl (p + 7) f (aLo & to32 (proj₂ m)) E1 tramp1 rT refl
  chain : Reach P nr arch args (p , acc) (E1 zl)
  chain = Reach-trans step0 (Reach-trans step1 joined)
pred-lemma pre rest (pmaskeq a m v) t f acc nr arch args =
  E1 el , chain , trans (cpc-if el (E2 eh) (f , aLo & to32 (proj₂ m))) (evalPredN-eq (pmaskeq a m v) args t f)
  where
  p = length pre
  R = compilePred p (pmaskeq a m v) t f ++ rest
  P = pre ++ R
  aHi = to32 (proj₁ (args a))
  aLo = to32 (proj₂ (args a))
  el = (aLo & to32 (proj₂ m)) ≡ᵇ to32 (proj₂ v)
  eh = (aHi & to32 (proj₁ m)) ≡ᵇ to32 (proj₁ v)
  H : ∀ j instr → atAbs R j ≡ just instr → atAbs P (p + j) ≡ just instr
  H j instr e = trans (atAbs-++ pre R j) e
  step0 : Reach P nr arch args (p , acc) (p + 1 , aLo)
  step0 = subst (λ z → Reach P nr arch args (p , acc) (p + 1 , z))
               (load-lo a nr arch args) (step (sLdAbs (H 0 (aLdAbs (off a)) refl)) refl)
  step1 : Reach P nr arch args (p + 1 , aLo) (p + 2 , aLo & to32 (proj₂ m))
  step1 = step (sAndImm (H 1 (aAndImm (to32 (proj₂ m))) refl)) refl
  tramp1 : Reach P nr arch args (p + 2 , aLo & to32 (proj₂ m))
             ((if (aLo & to32 (proj₂ m)) ≡ᵇ to32 (proj₂ v) then p + 7 else f) , aLo & to32 (proj₂ m))
  tramp1 = trampEval P (p + 2) (to32 (proj₂ v)) (p + 7) f (aLo & to32 (proj₂ m))
             (H 2 (aJeq (to32 (proj₂ v)) (p + 4) (p + 6)) refl)
             (H 4 (aJa (p + 7)) refl)
             (H 6 (aJa f) refl)
  step7 : Reach P nr arch args (p + 7 , aLo & to32 (proj₂ m)) (p + 8 , aHi)
  step7 = subst (λ z → Reach P nr arch args (p + 7 , aLo & to32 (proj₂ m)) (p + 8 , z))
               (load-hi a nr arch args) (step (sLdAbs (H 7 (aLdAbs (off a + 4)) refl)) refl)
  step8 : Reach P nr arch args (p + 8 , aHi) (p + 9 , aHi & to32 (proj₁ m))
  step8 = step (sAndImm (H 8 (aAndImm (to32 (proj₁ m))) refl)) refl
  tramp2 : Reach P nr arch args (p + 9 , aHi & to32 (proj₁ m))
             ((if (aHi & to32 (proj₁ m)) ≡ᵇ to32 (proj₁ v) then t else f) , aHi & to32 (proj₁ m))
  tramp2 = trampEval P (p + 9) (to32 (proj₁ v)) t f (aHi & to32 (proj₁ m))
             (H 9 (aJeq (to32 (proj₁ v)) (p + 11) (p + 13)) refl)
             (H 11 (aJa t) refl)
             (H 13 (aJa f) refl)
  from7 : Reach P nr arch args (p + 7 , aLo & to32 (proj₂ m))
            ((if eh then t else f) , aHi & to32 (proj₁ m))
  from7 = Reach-trans step7 (Reach-trans step8 tramp2)
  E2 : Bool → Conf
  E2 b = (if b then t else f) , (aHi & to32 (proj₁ m))
  E1 : Bool → Conf
  E1 b = if b then E2 eh else (f , aLo & to32 (proj₂ m))
  joined : Reach P nr arch args (p + 2 , aLo & to32 (proj₂ m)) (E1 el)
  joined = trampJoin el (p + 7) f (aLo & to32 (proj₂ m)) E1 tramp1 from7 refl
  chain : Reach P nr arch args (p , acc) (E1 el)
  chain = Reach-trans step0 (Reach-trans step1 joined)
pred-lemma pre rest (pand a b) t f acc nr arch args =
  E (evalPred a args) , joined , third
  where
  p = length pre
  A = compilePred p a (p + size a) f
  B = compilePred (p + size a) b t f
  R = (A ++ B) ++ rest
  P = pre ++ R
  cA = pred-lemma pre (B ++ rest) a (p + size a) f acc nr arch args
  cAc : Conf
  cAc = proj₁ cA
  cArc : Reach (pre ++ (A ++ (B ++ rest))) nr arch args (p , acc) cAc
  cArc = proj₁ (proj₂ cA)
  cAe : cpc cAc ≡ (if evalPred a args then (p + size a) else f)
  cAe = proj₂ (proj₂ cA)
  cB = pred-lemma (pre ++ A) rest b t f (cacc cAc) nr arch args
  CB = compilePred (length (pre ++ A)) b t f
  cBc : Conf
  cBc = proj₁ cB
  cBrc : Reach ((pre ++ A) ++ (CB ++ rest)) nr arch args (length (pre ++ A) , cacc cAc) cBc
  cBrc = proj₁ (proj₂ cB)
  cBe : cpc cBc ≡ (if evalPred b args then t else f)
  cBe = proj₂ (proj₂ cB)
  chainA_prog : Reach P nr arch args (p , acc) cAc
  chainA_prog = subst (λ ys → Reach ys nr arch args (p , acc) cAc)
                      (cong (pre ++_) (sym (++-assoc A B rest))) cArc
  chainA_rw : Reach P nr arch args (p , acc)
                ((if evalPred a args then (p + size a) else f) , cacc cAc)
  chainA_rw = subst (λ z → Reach P nr arch args (p , acc) (z , cacc cAc))
                    cAe chainA_prog
  lenAB : length (pre ++ A) ≡ p + size a
  lenAB = trans (length-++ pre {A}) (cong (p +_) (compilePred-length p a (p + size a) f))
  progeq : ((pre ++ A) ++ (CB ++ rest)) ≡ P
  progeq = trans (++-assoc pre A (CB ++ rest))
             (trans (cong (pre ++_) (cong (A ++_) (cong (_++ rest) (cong (λ z → compilePred z b t f) lenAB))))
                    (cong (pre ++_) (sym (++-assoc A B rest))))
  chainB_prog : Reach P nr arch args (p + size a , cacc cAc) cBc
  chainB_prog = subst (λ ys → Reach ys nr arch args (p + size a , cacc cAc) cBc)
                      progeq
                      (subst (λ z → Reach ((pre ++ A) ++ (CB ++ rest)) nr arch args (z , cacc cAc) cBc)
                             lenAB cBrc)
  E : Bool → Conf
  E b = if b then cBc else (f , cacc cAc)
  joined : Reach P nr arch args (p , acc) (E (evalPred a args))
  joined = endJoin (evalPred a args) (p + size a) f (cacc cAc) E chainA_rw chainB_prog refl
  third : cpc (E (evalPred a args)) ≡ (if evalPred (pand a b) args then t else f)
  third = trans (trans (cpc-if (evalPred a args) cBc (f , cacc cAc))
                       (cong (λ z → if evalPred a args then z else f) cBe))
                (if-∧ {evalPred a args} {evalPred b args} t f)
pred-lemma pre rest (por a b) t f acc nr arch args =
  E (evalPred a args) , joined , third
  where
  p = length pre
  A = compilePred p a t (p + size a)
  B = compilePred (p + size a) b t f
  R = (A ++ B) ++ rest
  P = pre ++ R
  cA = pred-lemma pre (B ++ rest) a t (p + size a) acc nr arch args
  cAc : Conf
  cAc = proj₁ cA
  cArc : Reach (pre ++ (A ++ (B ++ rest))) nr arch args (p , acc) cAc
  cArc = proj₁ (proj₂ cA)
  cAe : cpc cAc ≡ (if evalPred a args then t else (p + size a))
  cAe = proj₂ (proj₂ cA)
  cB = pred-lemma (pre ++ A) rest b t f (cacc cAc) nr arch args
  CB = compilePred (length (pre ++ A)) b t f
  cBc : Conf
  cBc = proj₁ cB
  cBrc : Reach ((pre ++ A) ++ (CB ++ rest)) nr arch args (length (pre ++ A) , cacc cAc) cBc
  cBrc = proj₁ (proj₂ cB)
  cBe : cpc cBc ≡ (if evalPred b args then t else f)
  cBe = proj₂ (proj₂ cB)
  chainA_prog : Reach P nr arch args (p , acc) cAc
  chainA_prog = subst (λ ys → Reach ys nr arch args (p , acc) cAc)
                      (cong (pre ++_) (sym (++-assoc A B rest))) cArc
  chainA_rw : Reach P nr arch args (p , acc)
                ((if evalPred a args then t else (p + size a)) , cacc cAc)
  chainA_rw = subst (λ z → Reach P nr arch args (p , acc) (z , cacc cAc))
                    cAe chainA_prog
  lenAB : length (pre ++ A) ≡ p + size a
  lenAB = trans (length-++ pre {A}) (cong (p +_) (compilePred-length p a t (p + size a)))
  progeq : ((pre ++ A) ++ (CB ++ rest)) ≡ P
  progeq = trans (++-assoc pre A (CB ++ rest))
             (trans (cong (pre ++_) (cong (A ++_) (cong (_++ rest) (cong (λ z → compilePred z b t f) lenAB))))
                    (cong (pre ++_) (sym (++-assoc A B rest))))
  chainB_prog : Reach P nr arch args (p + size a , cacc cAc) cBc
  chainB_prog = subst (λ ys → Reach ys nr arch args (p + size a , cacc cAc) cBc)
                      progeq
                      (subst (λ z → Reach ((pre ++ A) ++ (CB ++ rest)) nr arch args (z , cacc cAc) cBc)
                             lenAB cBrc)
  E : Bool → Conf
  E b = if b then (t , cacc cAc) else cBc
  joined : Reach P nr arch args (p , acc) (E (evalPred a args))
  joined = endJoin (evalPred a args) t (p + size a) (cacc cAc) E chainA_rw refl chainB_prog
  third : cpc (E (evalPred a args)) ≡ (if evalPred (por a b) args then t else f)
  third = trans (trans (cpc-if (evalPred a args) (t , cacc cAc) cBc)
                       (cong (λ z → if evalPred a args then t else z) cBe))
                (if-∨ {evalPred a args} {evalPred b args} t f)
