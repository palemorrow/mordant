module Mordant.RunDiff where

open import Data.Nat using (ℕ; zero; suc; _≡ᵇ_)
open import Data.Nat.Show using (show)
open import Data.Bool using (if_then_else_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (maybe′)
open import Data.String.Base using (_++_)
open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.String using (String)

open import Mordant.Policy using (Fixture; fArg; actionCode)
open import Mordant.Semantics using (evalPolicy)
open import Mordant.Lower using (compile)
open import Mordant.BPF using (runProgram)

postulate putStrLn : String → IO ⊤
{-# FOREIGN GHC import qualified Data.Text.IO as M #-}
{-# COMPILE GHC putStrLn = M.putStrLn #-}

open import Mordant.Fixtures using (fixtures)

runOne : Fixture → String
runOne f =
  maybe′ (λ n → if n ≡ᵇ actionCode (evalPolicy (Fixture.fPolicy f) (Fixture.fArch f) (Fixture.fNr f) (fArg f))
                  then show n else "-1") "-1"
    (runProgram (compile (Fixture.fPolicy f)) (Fixture.fArch f) (Fixture.fNr f) (fArg f))

render : List Fixture → ℕ → String
render [] _ = ""
render (f ∷ []) i = show i ++ " " ++ runOne f
render (f ∷ g ∷ fs) i = show i ++ " " ++ runOne f ++ "\n" ++ render (g ∷ fs) (suc i)

main : IO ⊤
main = putStrLn (render fixtures 0)
