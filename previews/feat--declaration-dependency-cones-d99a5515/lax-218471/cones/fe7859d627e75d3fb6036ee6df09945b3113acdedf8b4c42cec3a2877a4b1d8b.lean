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
namespace Lax218471.Programs.Executes
end Lax218471.Programs.Executes

namespace Lax218471.Programs.Program
end Lax218471.Programs.Program

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

namespace Lax218471.Programs

open Subroutine

variable {K A σ I : Type}

/-- One local operation; the control type is finite when programs are compiled. -/
inductive Op (K A σ : Type)
  | push (k : K) (f : σ → A)
  | pop (k : K) (f : σ → Option A → σ)
  | peek (k : K) (f : σ → Option A → σ)
  | load (f : σ → σ)

def Op.apply [DecidableEq K] (o : Op K A σ) (s : Store (fun _ : K => A) σ) :
    Store (fun _ : K => A) σ :=
  match o with
  | .push k f => ⟨s.state, Function.update s.stk k (f s.state :: s.stk k)⟩
  | .pop k f => ⟨f s.state (s.stk k).head?, Function.update s.stk k (s.stk k).tail⟩
  | .peek k f => ⟨f s.state (s.stk k).head?, s.stk⟩
  | .load f => ⟨f s.state, s.stk⟩

end Lax218471.Programs
end
