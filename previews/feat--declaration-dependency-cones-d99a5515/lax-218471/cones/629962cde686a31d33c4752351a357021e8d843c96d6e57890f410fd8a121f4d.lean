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

/-- Existence of a finite machine computing an encoded function in polynomial time. -/
def Polytime {α β A B : Type} (ea : α → List A) (eb : β → List B) (f : α → β) : Prop :=
  Nonempty (TM2ComputableInPolyTime ea eb f)

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

/-- The caller's initial or final store, with a single designated data stack. -/
def ioStore {K A σ : Type} [DecidableEq K]
    (port : K) (initial : σ) (xs : List A) : Store (fun _ : K => A) σ :=
  ⟨initial, Function.update (fun _ => []) port xs⟩

/-- Polynomially many source instructions and polynomially bounded calls
suffice for polynomial-time computation by an actual finite TM2. -/
axiom polytime {K A σ I : Type} [DecidableEq K] [Fintype A] [Inhabited A]
    [Fintype K] [Fintype σ] {α β : Type}
    (R : I → List A → List A → Prop)
    (library : ∀ i, Nonempty (Implementation (R i))) (p : Program K A σ I)
    (input output : K) (initial : σ) (ea : α → List A) (eb : β → List A) (f : α → β)
    (steps size : Polynomial ℕ)
    (h : ∀ a, ∃ n ≤ steps.eval (ea a).length,
      Executes R (size.eval (ea a).length) p
        (ioStore input initial (ea a)) (ioStore output initial (eb (f a))) n) :
    Polytime ea eb f

end Lax218471.Substitution
end
