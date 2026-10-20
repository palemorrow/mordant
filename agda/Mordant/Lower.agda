module Mordant.Lower where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Fin using (Fin; toℕ)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (length-++)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)

open import Mordant.Word using (to32; w32)
open import Mordant.Policy using (Pred; ptrue; peq; pne; plt; ple; pgt; pge;
  pmaskzero; pmaskeq; pand; por; actionCode; actKillProcess;
  Rule; Policy; policy; X32_BIT)
open import Mordant.Branch using (AbsInstr; aLdAbs; aLdImm; aAndImm; aJeq;
  aJgt; aJge; aJa; aRet; AbsProgram; relativize)
open import Mordant.BPF using (Program)

off : Fin 6 → ℕ
off a = 16 + 8 * toℕ a

testJeq : (i k t f : ℕ) → AbsProgram
testJeq i k t f = aJeq k (i + 2) (i + 4) ∷ aLdImm 0 ∷ aJa t ∷ aLdImm 0 ∷ aJa f ∷ []

testJgt : (i k t f : ℕ) → AbsProgram
testJgt i k t f = aJgt k (i + 2) (i + 4) ∷ aLdImm 0 ∷ aJa t ∷ aLdImm 0 ∷ aJa f ∷ []

testJge : (i k t f : ℕ) → AbsProgram
testJge i k t f = aJge k (i + 2) (i + 4) ∷ aLdImm 0 ∷ aJa t ∷ aLdImm 0 ∷ aJa f ∷ []

size : Pred → ℕ
size ptrue = 2
size (peq a c) = 12
size (pne a c) = 12
size (plt a c) = 17
size (ple a c) = 17
size (pgt a c) = 17
size (pge a c) = 17
size (pmaskzero a m) = 14
size (pmaskeq a m v) = 14
size (pand a b) = size a + size b
size (por a b) = size a + size b

compilePred : (s : ℕ) → Pred → (t f : ℕ) → AbsProgram
compilePred s ptrue t f = aLdImm 0 ∷ aJa t ∷ []
compilePred s (peq a c) t f =
  aLdAbs (off a + 4) ∷ testJeq (s + 1) (to32 (proj₁ c)) (s + 6) f
  ++ aLdAbs (off a) ∷ testJeq (s + 7) (to32 (proj₂ c)) t f
compilePred s (pne a c) t f = compilePred s (peq a c) f t
compilePred s (plt a c) t f =
  aLdAbs (off a + 4) ∷ testJgt (s + 1) (to32 (proj₁ c)) f (s + 6)
  ++ testJeq (s + 6) (to32 (proj₁ c)) (s + 11) t
  ++ aLdAbs (off a) ∷ testJge (s + 12) (to32 (proj₂ c)) f t
compilePred s (ple a c) t f =
  aLdAbs (off a + 4) ∷ testJgt (s + 1) (to32 (proj₁ c)) f (s + 6)
  ++ testJeq (s + 6) (to32 (proj₁ c)) (s + 11) t
  ++ aLdAbs (off a) ∷ testJgt (s + 12) (to32 (proj₂ c)) f t
compilePred s (pgt a c) t f =
  aLdAbs (off a + 4) ∷ testJgt (s + 1) (to32 (proj₁ c)) t (s + 6)
  ++ testJeq (s + 6) (to32 (proj₁ c)) (s + 11) f
  ++ aLdAbs (off a) ∷ testJgt (s + 12) (to32 (proj₂ c)) t f
compilePred s (pge a c) t f =
  aLdAbs (off a + 4) ∷ testJgt (s + 1) (to32 (proj₁ c)) t (s + 6)
  ++ testJeq (s + 6) (to32 (proj₁ c)) (s + 11) f
  ++ aLdAbs (off a) ∷ testJge (s + 12) (to32 (proj₂ c)) t f
compilePred s (pmaskzero a m) t f =
  aLdAbs (off a) ∷ aAndImm (to32 (proj₂ m)) ∷ testJeq (s + 2) 0 (s + 7) f
  ++ aLdAbs (off a + 4) ∷ aAndImm (to32 (proj₁ m)) ∷ testJeq (s + 9) 0 t f
compilePred s (pmaskeq a m v) t f =
  aLdAbs (off a) ∷ aAndImm (to32 (proj₂ m)) ∷ testJeq (s + 2) (to32 (proj₂ v)) (s + 7) f
  ++ aLdAbs (off a + 4) ∷ aAndImm (to32 (proj₁ m)) ∷ testJeq (s + 9) (to32 (proj₁ v)) t f
compilePred s (pand a b) t f =
  compilePred s a (s + size a) f ++ compilePred (s + size a) b t f
compilePred s (por a b) t f =
  compilePred s a t (s + size a) ++ compilePred (s + size a) b t f

compilePred-length : ∀ s pr t f → length (compilePred s pr t f) ≡ size pr
compilePred-length s ptrue t f = refl
compilePred-length s (peq a c) t f = refl
compilePred-length s (pne a c) t f = compilePred-length s (peq a c) f t
compilePred-length s (plt a c) t f = refl
compilePred-length s (ple a c) t f = refl
compilePred-length s (pgt a c) t f = refl
compilePred-length s (pge a c) t f = refl
compilePred-length s (pmaskzero a m) t f = refl
compilePred-length s (pmaskeq a m v) t f = refl
compilePred-length s (pand a b) t f =
  trans (length-++ (compilePred s a (s + size a) f))
    (trans (cong (_+ length (compilePred (s + size a) b t f))
                 (compilePred-length s a (s + size a) f))
           (cong (size a +_) (compilePred-length (s + size a) b t f)))
compilePred-length s (por a b) t f =
  trans (length-++ (compilePred s a t (s + size a)))
    (trans (cong (_+ length (compilePred (s + size a) b t f))
                 (compilePred-length s a t (s + size a)))
           (cong (size a +_) (compilePred-length (s + size a) b t f)))

ruleSize : Rule → ℕ
ruleSize r = 2 + (size (Rule.rulePred r) + 1)

rulesSize : List Rule → ℕ
rulesSize [] = 0
rulesSize (r ∷ rs) = ruleSize r + rulesSize rs

compileRule : (p : ℕ) → Rule → AbsProgram
compileRule p r =
  aLdAbs 0 ∷ aJeq (to32 (w32 (Rule.ruleNr r))) (p + 2) (p + ruleSize r)
  ∷ (compilePred (p + 2) (Rule.rulePred r) (p + 2 + size (Rule.rulePred r)) (p + ruleSize r)
     ++ aRet (actionCode (Rule.ruleAct r)) ∷ [])

compileRules : (p : ℕ) → List Rule → AbsProgram
compileRules p [] = []
compileRules p (r ∷ rs) = compileRule p r ++ compileRules (p + ruleSize r) rs

compileRule-length : ∀ p r → length (compileRule p r) ≡ ruleSize r
compileRule-length p r =
  trans (cong (2 +_)
          (length-++ (compilePred (p + 2) (Rule.rulePred r)
                        (p + 2 + size (Rule.rulePred r)) (p + ruleSize r))
                    {ys = aRet (actionCode (Rule.ruleAct r)) ∷ []}))
        (cong (2 +_) (cong (_+ 1)
          (compilePred-length (p + 2) (Rule.rulePred r)
            (p + 2 + size (Rule.rulePred r)) (p + ruleSize r))))

compileRules-length : ∀ p rules → length (compileRules p rules) ≡ rulesSize rules
compileRules-length p [] = refl
compileRules-length p (r ∷ rs) =
  trans (length-++ (compileRule p r))
    (trans (cong (_+ length (compileRules (p + ruleSize r) rs)) (compileRule-length p r))
           (cong (ruleSize r +_) (compileRules-length (p + ruleSize r) rs)))

compileAbs : Policy → AbsProgram
compileAbs (policy parm def rules) =
  aLdAbs 4 ∷ aJeq (to32 (w32 parm)) 2 (6 + rulesSize rules)
  ∷ aLdAbs 0 ∷ aAndImm X32_BIT ∷ aJeq 0 5 (6 + rulesSize rules)
  ∷ (compileRules 5 rules
     ++ aRet (actionCode def) ∷ aRet (actionCode actKillProcess) ∷ [])

progSize : List Rule → ℕ
progSize rules = 5 + (rulesSize rules + 2)

compileAbs-length : ∀ arch def rules → length (compileAbs (policy arch def rules)) ≡ 5 + (rulesSize rules + 2)
compileAbs-length arch def rules =
  trans (cong (5 +_)
          (length-++ (compileRules 5 rules)
                    {ys = aRet (actionCode def) ∷ aRet (actionCode actKillProcess) ∷ []}))
        (cong (5 +_) (cong (_+ 2) (compileRules-length 5 rules)))

compile : Policy → Program
compile p = relativize (compileAbs p)

compileTotal : Policy → Program
compileTotal = compile
