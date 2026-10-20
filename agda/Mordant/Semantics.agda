module Mordant.Semantics where

open import Data.Nat using (ℕ; _+_)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Bool using (Bool; true; false; _∧_; _∨_; not; if_then_else_)
open import Data.Maybe using (Maybe; just; nothing; fromMaybe)
open import Data.Product using (proj₁; proj₂)

open import Data.Nat using (_≡ᵇ_; _<ᵇ_; _≤ᵇ_)

open import Mordant.Word using (Word32; Word64; to32; to64; w32; _&_)
open import Mordant.Policy using (Pred; ptrue; peq; pne; plt; ple; pgt; pge;
  pmaskzero; pmaskeq; pand; por; Action; actAllow; actKillProcess; actErrno;
  Rule; Policy; policy; X32_BIT)

Env : Set
Env = Fin 6 → Word64

evalPred : Pred → Env → Bool
evalPred ptrue args = true
evalPred (peq a c) args = to64 (args a) ≡ᵇ to64 c
evalPred (pne a c) args = not (to64 (args a) ≡ᵇ to64 c)
evalPred (plt a c) args = to64 (args a) <ᵇ to64 c
evalPred (ple a c) args = to64 (args a) ≤ᵇ to64 c
evalPred (pgt a c) args = to64 c <ᵇ to64 (args a)
evalPred (pge a c) args = to64 c ≤ᵇ to64 (args a)
evalPred (pmaskzero a m) args =
  (to32 (proj₂ (args a)) & to32 (proj₂ m) ≡ᵇ 0) ∧
  (to32 (proj₁ (args a)) & to32 (proj₁ m) ≡ᵇ 0)
evalPred (pmaskeq a m v) args =
  (to32 (proj₂ (args a)) & to32 (proj₂ m) ≡ᵇ to32 (proj₂ v)) ∧
  (to32 (proj₁ (args a)) & to32 (proj₁ m) ≡ᵇ to32 (proj₁ v))
evalPred (pand a b) args = evalPred a args ∧ evalPred b args
evalPred (por a b) args = evalPred a args ∨ evalPred b args

evalRules : List Rule → ℕ → Env → Maybe Action
evalRules [] nr args = nothing
evalRules (r ∷ rs) nr args =
  if to32 (w32 (Rule.ruleNr r)) ≡ᵇ to32 (w32 nr)
    then (if evalPred (Rule.rulePred r) args then just (Rule.ruleAct r)
          else evalRules rs nr args)
    else evalRules rs nr args

evalPolicy : Policy → ℕ → ℕ → Env → Action
evalPolicy (policy parm def rules) arch nr args =
  if to32 (w32 arch) ≡ᵇ to32 (w32 parm)
    then (if to32 (w32 nr) & X32_BIT ≡ᵇ 0
            then fromMaybe def (evalRules rules nr args)
            else actKillProcess)
    else actKillProcess
