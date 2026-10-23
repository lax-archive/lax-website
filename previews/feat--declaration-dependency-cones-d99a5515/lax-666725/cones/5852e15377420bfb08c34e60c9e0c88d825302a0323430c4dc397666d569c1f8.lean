-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Computability.TuringMachine.PostTuringMachine
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Rat.Defs

-- Lax434930.PolynomialTime
section
namespace Lax434930
end Lax434930

namespace Lax434930.PolynomialTime
end Lax434930.PolynomialTime
end

-- Lax666725.ProbabilisticMachines
section
namespace Lax666725.ProbabilisticMachines.Procedure
end Lax666725.ProbabilisticMachines.Procedure

namespace Lax666725.ProbabilisticMachines

open Lax434930.PolynomialTime Turing

/-- Two finite local transition tables, with common halting configurations. -/
structure Machine where
  Γ : Type
  Q : Type
  [alphabet : Fintype Γ]
  [control : Fintype Q]
  [blank : Inhabited Γ]
  [initial : Inhabited Q]
  input : Bool ↪ Γ
  input_ne_blank : ∀ b, input b ≠ default
  transition : Bool → TM0.Machine Γ Q
  same_halts : ∀ q a, transition false q a = none ↔ transition true q a = none

attribute [instance] Machine.alphabet Machine.control Machine.blank Machine.initial

end Lax666725.ProbabilisticMachines
end
