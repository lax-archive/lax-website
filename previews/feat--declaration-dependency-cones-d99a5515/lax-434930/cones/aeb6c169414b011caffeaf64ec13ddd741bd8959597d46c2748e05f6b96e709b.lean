-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Computability.TuringMachine.PostTuringMachine

-- Lax434930.PolynomialTime
section
namespace Lax434930.PolynomialTime

/-- A finite binary string. -/
abbrev Word := List Bool

/-- A language of finite binary strings. -/
abbrev Language := Set Word

/-- Languages whose Boolean characteristic functions are computable in polynomial time. -/
def P : Set Language :=
  {L | ∃ f : Word → Bool,
    (∀ w, f w = true ↔ w ∈ L) ∧
    Nonempty (Turing.TM2ComputableInPolyTime id Computability.encodeBool f)}

end Lax434930.PolynomialTime
end

-- Lax434930.MachineModels
section
namespace Lax434930.MachineModels

open Turing PolynomialTime

/-- Polynomial-time stack deciders with finite alphabets at every stack. -/
def FiniteStackP : Set Language :=
  {L | ∃ (f : Word → Bool)
    (M : TM2ComputableInPolyTime id Computability.encodeBool f),
    (∀ w, f w = true ↔ w ∈ L) ∧ ∀ k, Finite (M.tm.Γ k)}

/-- A finite elementary single-tape machine, with ordinary binary input. -/
structure SingleTape where
  Γ : Type
  Q : Type
  [alphabet : Fintype Γ]
  [control : Fintype Q]
  [blank : Inhabited Γ]
  [initial : Inhabited Q]
  input : Bool ↪ Γ
  input_ne_blank : ∀ b, input b ≠ default
  transition : TM0.Machine Γ Q
  accept : Q → Bool

attribute [instance] SingleTape.alphabet SingleTape.control SingleTape.blank SingleTape.initial

end Lax434930.MachineModels
end

-- Lax434930.FiniteStackEquivalence
section
namespace Lax434930.FiniteStackEquivalence

open PolynomialTime MachineModels

/-- Requiring all work alphabets to be finite does not change P. -/
axiom finiteStackP_eq_P : FiniteStackP = P

end Lax434930.FiniteStackEquivalence
end
