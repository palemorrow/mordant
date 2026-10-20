module Mordant.BPF where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _/_)
open import Data.Nat using (_≡ᵇ_; _<ᵇ_; _≤ᵇ_)
open import Data.Nat.DivMod using (_%_)
open import Data.Fin as F using (Fin)
open import Data.List using (List; []; _∷_; length)
open import Data.Bool using (Bool; true; false; _∧_; if_then_else_)
open import Data.Maybe using (Maybe; just; nothing; maybe′)
open import Data.Maybe.Properties using (just-injective)
open import Data.Empty using (⊥-elim)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; _≢_)

open import Mordant.Word using (Word32; to32; w32; _&_)
open import Mordant.Semantics using (Env)

data Instr : Set where
  ldAbs : ℕ → Instr
  ldImm : ℕ → Instr
  andImm : ℕ → Instr
  jeq : (k jt jf : ℕ) → Instr
  jgt : (k jt jf : ℕ) → Instr
  jge : (k jt jf : ℕ) → Instr
  ja : (k : ℕ) → Instr
  ret : (k : ℕ) → Instr

Program : Set
Program = List Instr

atWord : List Word32 → ℕ → Maybe Word32
atWord [] _ = nothing
atWord (w ∷ _) zero = just w
atWord (_ ∷ ws) (suc n) = atWord ws n

atInstr : Program → ℕ → Maybe Instr
atInstr [] _ = nothing
atInstr (i ∷ _) zero = just i
atInstr (_ ∷ is) (suc n) = atInstr is n

argWords : Env → List Word32
argWords args =
  proj₂ (args F.zero) ∷ proj₁ (args F.zero) ∷
  proj₂ (args (F.suc F.zero)) ∷ proj₁ (args (F.suc F.zero)) ∷
  proj₂ (args (F.suc (F.suc F.zero))) ∷ proj₁ (args (F.suc (F.suc F.zero))) ∷
  proj₂ (args (F.suc (F.suc (F.suc F.zero)))) ∷
    proj₁ (args (F.suc (F.suc (F.suc F.zero)))) ∷
  proj₂ (args (F.suc (F.suc (F.suc (F.suc F.zero))))) ∷
    proj₁ (args (F.suc (F.suc (F.suc (F.suc F.zero))))) ∷
  proj₂ (args (F.suc (F.suc (F.suc (F.suc (F.suc F.zero)))))) ∷
    proj₁ (args (F.suc (F.suc (F.suc (F.suc (F.suc F.zero)))))) ∷
  []

ctxWords : ℕ → ℕ → Env → List Word32
ctxWords nr arch args = w32 nr ∷ w32 arch ∷ w32 0 ∷ w32 0 ∷ argWords args

loadWord : ℕ → ℕ → ℕ → Env → ℕ
loadWord k nr arch args with atWord (ctxWords nr arch args) (k / 4)
... | nothing = 0
... | just w = to32 w

load-lo : ∀ (a : Fin 6) nr arch args →
  loadWord (16 + 8 * F.toℕ a) nr arch args ≡ to32 (proj₂ (args a))
load-lo F.zero nr arch args = refl
load-lo (F.suc F.zero) nr arch args = refl
load-lo (F.suc (F.suc F.zero)) nr arch args = refl
load-lo (F.suc (F.suc (F.suc F.zero))) nr arch args = refl
load-lo (F.suc (F.suc (F.suc (F.suc F.zero)))) nr arch args = refl
load-lo (F.suc (F.suc (F.suc (F.suc (F.suc F.zero))))) nr arch args = refl

load-hi : ∀ (a : Fin 6) nr arch args →
  loadWord (16 + 8 * F.toℕ a + 4) nr arch args ≡ to32 (proj₁ (args a))
load-hi F.zero nr arch args = refl
load-hi (F.suc F.zero) nr arch args = refl
load-hi (F.suc (F.suc F.zero)) nr arch args = refl
load-hi (F.suc (F.suc (F.suc F.zero))) nr arch args = refl
load-hi (F.suc (F.suc (F.suc (F.suc F.zero)))) nr arch args = refl
load-hi (F.suc (F.suc (F.suc (F.suc (F.suc F.zero))))) nr arch args = refl

mutual
  run : Program → ℕ → ℕ → ℕ → ℕ → ℕ → Env → Maybe ℕ
  run xs zero pc acc nr arch args = nothing
  run xs (suc f) pc acc nr arch args =
    maybe′ (runInstr xs f pc acc nr arch args) nothing (atInstr xs pc)

  runInstr : Program → ℕ → ℕ → ℕ → ℕ → ℕ → Env → Instr → Maybe ℕ
  runInstr xs f pc acc nr arch args (ldAbs k) =
    run xs f (suc pc) (loadWord k nr arch args) nr arch args
  runInstr xs f pc acc nr arch args (ldImm k) = run xs f (suc pc) k nr arch args
  runInstr xs f pc acc nr arch args (andImm k) = run xs f (suc pc) (acc & k) nr arch args
  runInstr xs f pc acc nr arch args (jeq k jt jf) =
    run xs f (suc pc + (if acc ≡ᵇ k then jt else jf)) acc nr arch args
  runInstr xs f pc acc nr arch args (jgt k jt jf) =
    run xs f (suc pc + (if k <ᵇ acc then jt else jf)) acc nr arch args
  runInstr xs f pc acc nr arch args (jge k jt jf) =
    run xs f (suc pc + (if k ≤ᵇ acc then jt else jf)) acc nr arch args
  runInstr xs f pc acc nr arch args (ja k) = run xs f (suc pc + k) acc nr arch args
  runInstr xs f pc acc nr arch args (ret k) = just k

runProgram : Program → ℕ → ℕ → Env → Maybe ℕ
runProgram xs arch nr args = run xs (length xs) 0 0 nr arch args

nothing≢just : ∀ {A : Set} {i : A} → nothing ≢ just i
nothing≢just ()

run-unfold : ∀ xs f pc acc nr arch args {i} → atInstr xs pc ≡ just i →
  run xs (suc f) pc acc nr arch args ≡ runInstr xs f pc acc nr arch args i
run-unfold xs f pc acc nr arch args {i} eq =
  cong (maybe′ (runInstr xs f pc acc nr arch args) nothing) eq

isRet : Instr → Bool
isRet (ret _) = true
isRet _ = false

validInstr : Instr → ℕ → ℕ → Bool
validInstr (ldAbs k) pc n = (k % 4 ≡ᵇ 0) ∧ (k + 4 ≤ᵇ 64)
validInstr (ldImm k) pc n = true
validInstr (andImm k) pc n = true
validInstr (jeq k jt jf) pc n = (suc pc + jt <ᵇ n) ∧ (suc pc + jf <ᵇ n)
validInstr (jgt k jt jf) pc n = (suc pc + jt <ᵇ n) ∧ (suc pc + jf <ᵇ n)
validInstr (jge k jt jf) pc n = (suc pc + jt <ᵇ n) ∧ (suc pc + jf <ᵇ n)
validInstr (ja k) pc n = suc pc + k <ᵇ n
validInstr (ret k) pc n = true

validFrom : Program → ℕ → ℕ → Bool
validFrom [] pc n = true
validFrom (i ∷ is) pc n = validInstr i pc n ∧ validFrom is (suc pc) n

endsRet : Program → Bool
endsRet [] = false
endsRet (i ∷ []) = isRet i
endsRet (_ ∷ is) = endsRet is

valid : Program → Bool
valid xs = validFrom xs 0 (length xs) ∧ endsRet xs
