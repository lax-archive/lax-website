-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum

-- Lax218471.Subroutine
section
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

instance : DecidableEq p.W := p.workEq

/-- A boundary configuration contains no private working data. -/
def boundary (l : Option p.Label) (s : Store Γ σ) :
    TM2.Cfg (Sum.elim Γ p.Δ) p.Label (σ × p.τ) where
  l := l
  var := (s.state, p.initial)
  stk := fun | .inl k => s.stk k | .inr _ => []

/-- Exact execution from a clean entry to a clean return. -/
def Executes [DecidableEq K] (s t : Store Γ σ) (n : ℕ) : Prop :=
  (fun c => c.bind (TM2.step p.code))^[n] (some (p.boundary (some p.entry) s)) =
    some (p.boundary none t)

end Routine

end Lax218471.Subroutine
end
