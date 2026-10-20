module Mordant.Policy where

open import Data.Nat using (ℕ; _+_)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; length)
open import Data.Product using (_×_; proj₁; proj₂)
open import Mordant.Word using (Word64)

AUDIT_ARCH_X86-64 : ℕ
AUDIT_ARCH_X86-64 = 0xC000003E

X32_BIT : ℕ
X32_BIT = 0x40000000

data Pred : Set where
  ptrue : Pred
  peq : (arg : Fin 6) (c : Word64) → Pred
  pne : (arg : Fin 6) (c : Word64) → Pred
  plt : (arg : Fin 6) (c : Word64) → Pred
  ple : (arg : Fin 6) (c : Word64) → Pred
  pgt : (arg : Fin 6) (c : Word64) → Pred
  pge : (arg : Fin 6) (c : Word64) → Pred
  pmaskzero : (arg : Fin 6) (mask : Word64) → Pred
  pmaskeq : (arg : Fin 6) (mask : Word64) (v : Word64) → Pred
  pand : (a b : Pred) → Pred
  por : (a b : Pred) → Pred

data Action : Set where
  actAllow : Action
  actKillProcess : Action
  actErrno : ℕ → Action

actionCode : Action → ℕ
actionCode actAllow = 0x7fff0000
actionCode actKillProcess = 0x80000000
actionCode (actErrno n) = 0x00050000 + n

record Rule : Set where
  constructor rule
  field
    ruleNr : ℕ
    rulePred : Pred
    ruleAct : Action

data Policy : Set where
  policy : (arch : ℕ) (def : Action) (rules : List Rule) → Policy

record Fixture : Set where
  field
    fArch : ℕ
    fNr : ℕ
    fArgs : Word64 × Word64 × Word64 × Word64 × Word64 × Word64
    fPolicy : Policy

fArg : Fixture → Fin 6 → Word64
fArg f zero = proj₁ (Fixture.fArgs f)
fArg f (suc zero) = proj₁ (proj₂ (Fixture.fArgs f))
fArg f (suc (suc zero)) = proj₁ (proj₂ (proj₂ (Fixture.fArgs f)))
fArg f (suc (suc (suc zero))) = proj₁ (proj₂ (proj₂ (proj₂ (Fixture.fArgs f))))
fArg f (suc (suc (suc (suc zero)))) =
  proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (Fixture.fArgs f)))))
fArg f (suc (suc (suc (suc (suc zero))))) =
  proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (Fixture.fArgs f)))))
