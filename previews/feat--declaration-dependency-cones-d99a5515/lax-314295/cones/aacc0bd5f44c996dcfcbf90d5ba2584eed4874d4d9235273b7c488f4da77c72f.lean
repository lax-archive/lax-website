-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Computability.DFA
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Logic.Function.Iterate

-- Lax765601.MealyMachine
section
namespace Lax765601
end Lax765601

namespace Lax765601.MealyMachine
end Lax765601.MealyMachine

namespace Lax765601.MealyMachine.Mealy
end Lax765601.MealyMachine.Mealy

namespace Lax765601.MealyMachine.Mealy.run
end Lax765601.MealyMachine.Mealy.run
end

-- Lax765601.StateTransformations
section
namespace Lax765601.StateTransformations

open Lax765601.MealyMachine

/-- The state transformation of an input string, for the pre-automaton `δ`: the
letters act one after the other, in reading order. -/
def strTrans {A Q : Type} (δ : Q → A → Q) (w : List A) : Q → Q := fun q => w.foldl δ q

/-- The stabilisation condition (*) of Lemma A.2.11: for every state
transformation `δ_w` arising from an input string, the sequence of its powers
`δ_w¹, δ_w², …` eventually stabilises. -/
def TransAperiodic {A Q : Type} (δ : Q → A → Q) : Prop :=
  ∀ w : List A, ∃ N : ℕ, ∀ n ≥ N, (strTrans δ w)^[n] = (strTrans δ w)^[N]

end Lax765601.StateTransformations
end

-- Lax132576.Bimachines
section
namespace Lax132576.Bimachines

open Lax765601.StateTransformations

/-- A bimachine: a deterministic prefix automaton, a deterministic suffix automaton
(run on the reverse of the suffix) and an output function on pairs of states. -/
structure Bimachine (A B P S : Type) where
  /-- Initial state of the prefix automaton. -/
  prefixInit : P
  /-- Transition function of the prefix automaton. -/
  prefixStep : P → A → P
  /-- Initial state of the suffix automaton. -/
  suffixInit : S
  /-- Transition function of the suffix automaton. -/
  suffixStep : S → A → S
  /-- The output function. -/
  out : P → S → List B

namespace Bimachine

variable {A B P S : Type}

/-- The semantics of a bimachine: for every gap `i` of the input, the prefix
automaton is run on the first `i` letters and the suffix automaton on the reverse
of the rest, and the pieces of output are concatenated. -/
def eval (M : Bimachine A B P S) (w : List A) : List B :=
  ((List.range (w.length + 1)).map (fun i =>
    M.out (strTrans M.prefixStep (w.take i) M.prefixInit)
          (strTrans M.suffixStep (w.drop i).reverse M.suffixInit))).flatten

end Bimachine

/-- A function computed by an aperiodic bimachine: both automata satisfy the
stabilisation condition on their state transformations. -/
def IsAperiodicBimachine {A B : Type} (f : List A → List B) : Prop :=
  ∃ (P S : Type) (_ : Finite P) (_ : Finite S) (M : Bimachine A B P S),
    M.eval = f ∧ TransAperiodic M.prefixStep ∧ TransAperiodic M.suffixStep

end Lax132576.Bimachines
end

-- Lax314295.MSOLogic
section
namespace Lax314295.MSOLogic

/-- Formulas of monadic second-order logic over strings with letters in `A`;
first-order and second-order variables are named by natural numbers. -/
inductive MSO (A : Type) : Type
  /-- The order test `x_i ≤ x_j`. -/
  | le : ℕ → ℕ → MSO A
  /-- The label test `a (x_i)`. -/
  | lab : A → ℕ → MSO A
  /-- The membership test `x_i ∈ X_j`. -/
  | mem : ℕ → ℕ → MSO A
  /-- Negation. -/
  | not : MSO A → MSO A
  /-- Conjunction. -/
  | and : MSO A → MSO A → MSO A
  /-- Disjunction. -/
  | or : MSO A → MSO A → MSO A
  /-- First-order existential quantification `∃ x_i`. -/
  | exFO : ℕ → MSO A → MSO A
  /-- Second-order existential quantification `∃ X_i`. -/
  | exSO : ℕ → MSO A → MSO A

namespace MSO

variable {A : Type}

/-- Satisfaction of a formula in a string under a valuation of the first-order
variables by positions and of the second-order variables by sets of positions. -/
def Sat (w : List A) : (ℕ → ℕ) → (ℕ → Set ℕ) → MSO A → Prop
  | fo, _, le i j => fo i ≤ fo j
  | fo, _, lab a i => w[fo i]? = some a
  | fo, so, mem i j => fo i ∈ so j
  | fo, so, not φ => ¬ Sat w fo so φ
  | fo, so, and φ ψ => Sat w fo so φ ∧ Sat w fo so ψ
  | fo, so, or φ ψ => Sat w fo so φ ∨ Sat w fo so ψ
  | fo, so, exFO i φ => ∃ p < w.length, Sat w (Function.update fo i p) so φ
  | fo, so, exSO i φ => ∃ S ⊆ {p | p < w.length}, Sat w fo (Function.update so i S) φ

/-- A formula is first-order if it uses neither set quantification nor membership.
-/
def IsFO : MSO A → Prop
  | le _ _ => True
  | lab _ _ => True
  | mem _ _ => False
  | not φ => IsFO φ
  | and φ ψ => IsFO φ ∧ IsFO ψ
  | or φ ψ => IsFO φ ∧ IsFO ψ
  | exFO _ φ => IsFO φ
  | exSO _ _ => False

end MSO

end Lax314295.MSOLogic
end

-- Lax314295.MSORelabellings
section
namespace Lax314295.MSORelabellings

open Lax314295.MSOLogic

/-- An mso relabelling: a finite family of formulas with one free first-order
variable (the variable `0`), exactly one of which holds at each position of each
input, an output string for each formula, and an output for the empty input. -/
structure MSORelabelling (A B : Type) where
  /-- The index set of the formulas. -/
  Idx : Type
  /-- Finiteness of the index set. -/
  finIdx : Finite Idx
  /-- The formulas, each with the one free first-order variable `x₀`. -/
  form : Idx → MSO A
  /-- The output string of each formula. -/
  out : Idx → List B
  /-- The output string for the empty input. -/
  emptyOut : List B
  /-- At every position of every input string exactly one formula holds. -/
  unique : ∀ (w : List A) (p : ℕ), p < w.length →
    ∃! i : Idx, MSO.Sat w (fun _ => p) (fun _ => ∅) (form i)

namespace MSORelabelling

variable {A B : Type}

/-- The relabelling maps `w` to `v`: for a nonempty input, `v` is the concatenation
of the outputs of the formulas true at the positions of `w`; the empty input
gives the designated string. -/
def Relabels (R : MSORelabelling A B) (w : List A) (v : List B) : Prop :=
  (w = [] ∧ v = R.emptyOut) ∨
  (w ≠ [] ∧ ∃ g : ℕ → R.Idx,
    (∀ p < w.length, MSO.Sat w (fun _ => p) (fun _ => ∅) (R.form (g p))) ∧
    v = ((List.range w.length).map (fun p => R.out (g p))).flatten)

/-- All formulas of the relabelling are first-order. -/
def AllFO (R : MSORelabelling A B) : Prop := ∀ i, (R.form i).IsFO

end MSORelabelling

/-- A function defined by a first-order relabelling. -/
def IsFORelabelling {A B : Type} (f : List A → List B) : Prop :=
  ∃ R : MSORelabelling A B, R.AllFO ∧ ∀ w, R.Relabels w (f w)

end Lax314295.MSORelabellings
end

-- Lax314295.AperiodicBimachineOfFORelabelling
section
namespace Lax314295.AperiodicBimachineOfFORelabelling

open Lax132576.Bimachines Lax314295.MSORelabellings

/-- A first-order relabelling is computed by an aperiodic bimachine. -/
axiom isAperiodicBimachine_of_isFORelabelling {A B : Type} [Finite A] [Finite B]
    {f : List A → List B} (hf : IsFORelabelling f) : IsAperiodicBimachine f

end Lax314295.AperiodicBimachineOfFORelabelling
end
