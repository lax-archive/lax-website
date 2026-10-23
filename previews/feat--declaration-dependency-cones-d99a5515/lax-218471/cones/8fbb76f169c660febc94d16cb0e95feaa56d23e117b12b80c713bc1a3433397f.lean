-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum

-- Lax218471.PolynomialTime
section
namespace Lax218471.PolynomialTime

open Turing

/-- A finite machine and a time bound realizing every input/output pair of a contract. -/
structure Implementation {A : Type} (R : List A → List A → Prop) extends
    TM2ComputableAux A A where
  time : Polynomial ℕ
  correct : ∀ x y, R x y →
    Nonempty (TM2OutputsInTime tm (x.map inputAlphabet.symm)
      (some (y.map outputAlphabet.symm)) (time.eval x.length))

end Lax218471.PolynomialTime
end

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

-- Lax218471.Programs
section
namespace Lax218471.Programs

open Subroutine

variable {K A σ I : Type}

/-- One local operation; the control type is finite when programs are compiled. -/
inductive Op (K A σ : Type)
  | push (k : K) (f : σ → A)
  | pop (k : K) (f : σ → Option A → σ)
  | peek (k : K) (f : σ → Option A → σ)
  | load (f : σ → σ)

/-- A finite program with named library calls. Loops retain their body as finite code. -/
inductive Program (K A σ I : Type)
  | atom (o : Op K A σ)
  | call (i : I) (port : K)
  | seq (p q : Program K A σ I)
  | branch (b : σ → Bool) (p q : Program K A σ I)
  | loop (b : σ → Bool) (p : Program K A σ I)

def Op.apply [DecidableEq K] (o : Op K A σ) (s : Store (fun _ : K => A) σ) :
    Store (fun _ : K => A) σ :=
  match o with
  | .push k f => ⟨s.state, Function.update s.stk k (f s.state :: s.stk k)⟩
  | .pop k f => ⟨f s.state (s.stk k).head?, Function.update s.stk k (s.stk k).tail⟩
  | .peek k f => ⟨f s.state (s.stk k).head?, s.stk⟩
  | .load f => ⟨f s.state, s.stk⟩

/-- Source execution, with a bound on the length of every argument and reply. -/
inductive Executes [DecidableEq K] (R : I → List A → List A → Prop) (size : ℕ) :
    Program K A σ I → Store (fun _ : K => A) σ → Store (fun _ : K => A) σ → ℕ → Prop
  | atom (o) (s) : Executes R size (.atom o) s (o.apply s) 1
  | call (i) (port) (s) (y) : R i (s.stk port) y →
      (s.stk port).length ≤ size → y.length ≤ size →
      Executes R size (.call i port) s ⟨s.state, Function.update s.stk port y⟩ 1
  | seq {p q s u t a b} : Executes R size p s u a → Executes R size q u t b →
      Executes R size (.seq p q) s t (a + b)
  | branch_true {p q s t a} {b : σ → Bool} : b s.state = true →
      Executes R size p s t a → Executes R size (.branch b p q) s t (a + 1)
  | branch_false {p q s t a} {b : σ → Bool} : b s.state = false →
      Executes R size q s t a → Executes R size (.branch b p q) s t (a + 1)
  | loop_false {p s} {b : σ → Bool} : b s.state = false →
      Executes R size (.loop b p) s s 1
  | loop_true {p s u t a c} {b : σ → Bool} : b s.state = true →
      Executes R size p s u a → Executes R size (.loop b p) u t c →
      Executes R size (.loop b p) s t (a + c + 1)

end Lax218471.Programs
end

-- Lax218471.Substitution
section
namespace Lax218471.Substitution

open Subroutine Programs PolynomialTime

/-- Compilation to a concrete subroutine, with polynomial overhead per source
instruction in the maximum call argument and reply length. -/
axiom compile {K A σ I : Type} [DecidableEq K] [Fintype A] [Inhabited A]
    (R : I → List A → List A → Prop)
    (library : ∀ i, Nonempty (Implementation (R i))) (p : Program K A σ I) :
    ∃ (r : Routine (fun _ : K => A) σ) (overhead : Polynomial ℕ),
      ∀ size s t n, Executes R size p s t n →
        ∃ m ≤ n * overhead.eval size, r.Executes s t m

end Lax218471.Substitution
end
