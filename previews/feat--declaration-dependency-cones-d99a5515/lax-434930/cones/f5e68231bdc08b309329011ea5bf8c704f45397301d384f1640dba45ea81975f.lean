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

end Lax434930.PolynomialTime
end

-- Lax434930.MachineModels
section
namespace Lax434930.MachineModels

open Turing PolynomialTime

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

/-- The standard single-tape formulation: one machine and one polynomial,
halting on every input, with acceptance exactly matching membership. -/
def SingleTapeP : Set Language :=
  {L | ∃ (M : SingleTape) (p : Polynomial ℕ), ∀ w : Word,
    ∃ c : TM0.Cfg M.Γ M.Q,
      Nonempty (StateTransition.EvalsToInTime (TM0.step M.transition)
        (TM0.init (w.map M.input)) (some c) (p.eval w.length)) ∧
      TM0.step M.transition c = none ∧ (M.accept c.q = true ↔ w ∈ L)}

end Lax434930.MachineModels
end

-- Lax434930.SingleTapeComplement
section
namespace Lax434930.SingleTapeComplement

open PolynomialTime MachineModels

/-- Complement closure for the elementary single-tape definition. -/
axiom closed_under_complement (L : Language) :
  L ∈ SingleTapeP → Lᶜ ∈ SingleTapeP

end Lax434930.SingleTapeComplement
end
