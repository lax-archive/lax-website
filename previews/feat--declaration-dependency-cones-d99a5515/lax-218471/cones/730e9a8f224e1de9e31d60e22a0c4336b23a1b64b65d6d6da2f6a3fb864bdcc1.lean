-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum

-- Lax218471.PolynomialTime
section
namespace Lax218471
end Lax218471

namespace Lax218471.PolynomialTime
end Lax218471.PolynomialTime

namespace Lax218471.PolynomialTime.Implementation
end Lax218471.PolynomialTime.Implementation
end

-- Lax218471.Subroutine
section
namespace Lax218471.Subroutine.Routine.boundary
end Lax218471.Subroutine.Routine.boundary

namespace Lax218471.Subroutine

open Turing

/-- The data visible to a caller between subroutine calls. -/
structure Store {K : Type} (Γ : K → Type) (σ : Type) where
  state : σ
  stk : ∀ k, List (Γ k)

/-- An ordinary finite TM2 program with a private working region. -/
structure Routine {K : Type} (Γ : K → Type) (σ : Type) where
  W : Type
  [workEq : DecidableEq W]
  [workFin : Fintype W]
  Δ : W → Type
  τ : Type
  [stateFin : Fintype τ]
  initial : τ
  Label : Type
  [labelFin : Fintype Label]
  entry : Label
  code : Label → TM2.Stmt (Sum.elim Γ Δ) Label (σ × τ)

namespace Routine

variable {K σ : Type} {Γ : K → Type} (p : Routine Γ σ)

end Routine

end Lax218471.Subroutine
end

-- Lax218471.Programs
section
namespace Lax218471.Programs
end Lax218471.Programs

namespace Lax218471.Programs.Executes
end Lax218471.Programs.Executes

namespace Lax218471.Programs.Op
end Lax218471.Programs.Op

namespace Lax218471.Programs.Program
end Lax218471.Programs.Program

namespace Lax218471.Programs.Op.apply
end Lax218471.Programs.Op.apply

namespace Lax218471.Programs.Op.load
end Lax218471.Programs.Op.load

namespace Lax218471.Programs.Op.peek
end Lax218471.Programs.Op.peek

namespace Lax218471.Programs.Op.pop
end Lax218471.Programs.Op.pop

namespace Lax218471.Programs.Op.push
end Lax218471.Programs.Op.push

namespace Lax218471.Programs.Program.atom
end Lax218471.Programs.Program.atom

namespace Lax218471.Programs.Program.branch
end Lax218471.Programs.Program.branch

namespace Lax218471.Programs.Program.call
end Lax218471.Programs.Program.call

namespace Lax218471.Programs.Program.loop
end Lax218471.Programs.Program.loop

namespace Lax218471.Programs.Program.seq
end Lax218471.Programs.Program.seq
end

-- Lax218471.Substitution
section
namespace Lax218471.Substitution

open Subroutine Programs PolynomialTime

/-- The caller's initial or final store, with a single designated data stack. -/
def ioStore {K A σ : Type} [DecidableEq K]
    (port : K) (initial : σ) (xs : List A) : Store (fun _ : K => A) σ :=
  ⟨initial, Function.update (fun _ => []) port xs⟩

end Lax218471.Substitution
end
