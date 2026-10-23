-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Log

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

-- Lax434930.SpaceMachines
section
namespace Lax434930.SpaceMachines.Configuration
end Lax434930.SpaceMachines.Configuration

namespace Lax434930.SpaceMachines.readInput
end Lax434930.SpaceMachines.readInput

namespace Lax434930.SpaceMachines.Machine.Run
end Lax434930.SpaceMachines.Machine.Run

namespace Lax434930.SpaceMachines.Move.apply
end Lax434930.SpaceMachines.Move.apply

set_option backward.isDefEq.respectTransparency false

namespace Lax434930.SpaceMachines

open PolynomialTime

/-- The input alphabet, with two distinct endmarkers. -/
inductive InputSymbol
  | leftEnd
  | bit (value : Bool)
  | rightEnd
  deriving DecidableEq, Fintype

/-- An elementary head movement, including staying in place. -/
inductive Move
  | left
  | stay
  | right
  deriving DecidableEq, Fintype

/-- One local transition: change state, write a work symbol, and move the heads. -/
structure Action (Γ Q : Type) where
  state : Q
  write : Γ
  inputMove : Move
  workMove : Move

/-- The complete finite description of a possibly nondeterministic machine. -/
structure Machine where
  Γ : Type
  Q : Type
  [alphabet : Fintype Γ]
  [control : Fintype Q]
  blank : Γ
  start : Q
  transition : Q → InputSymbol → Γ → Finset (Action Γ Q)
  accept : Q → Bool

attribute [instance] Machine.alphabet Machine.control

end Lax434930.SpaceMachines
end

-- Lax434930.SpaceBounds
section
namespace Lax434930.SpaceBounds
end Lax434930.SpaceBounds
end

-- Lax434930.NondeterministicLogarithmicSpace
section
namespace Lax434930.NondeterministicLogarithmicSpace
end Lax434930.NondeterministicLogarithmicSpace
end

-- Lax434930.Certificates
section
namespace Lax434930.Certificates.unpair
end Lax434930.Certificates.unpair

namespace Lax434930.Certificates

open PolynomialTime

/-- A self-delimiting encoding of the first string, followed by the second. -/
def pair : Word → Word → Word
  | [], y => true :: y
  | b :: x, y => false :: b :: pair x y

end Lax434930.Certificates
end

-- Lax434930.NondeterministicPolynomialTime
section
namespace Lax434930.NondeterministicPolynomialTime

open PolynomialTime Certificates

/-- Languages with polynomially bounded, polynomial-time verifiable certificates. -/
def NP : Set Language :=
  {A | ∃ V : Language, V ∈ P ∧ ∃ p : Polynomial ℕ, ∀ x : Word,
    x ∈ A ↔ ∃ y : Word, y.length ≤ p.eval x.length ∧ pair x y ∈ V}

end Lax434930.NondeterministicPolynomialTime
end

-- Lax434930.ComplementClasses
section
namespace Lax434930.ComplementClasses

open PolynomialTime NondeterministicLogarithmicSpace NondeterministicPolynomialTime

/-- The class of languages whose complements belong to the given class. -/
def co (C : Set Language) : Set Language := {A | Aᶜ ∈ C}

/-- Complements of languages in NP. -/
def coNP : Set Language := co NP

end Lax434930.ComplementClasses
end
