-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Set.Finite.Basic

-- Lax132576.LabelledAutomata
section
namespace Lax132576.LabelledAutomata

/-- An automaton whose finitely many transitions are labelled by an input string and
a label from `L`, with distinguished sets of initial and final states. -/
structure LabAut (A L Q : Type) where
  /-- The set of initial states. -/
  init : Set Q
  /-- The set of final states. -/
  final : Set Q
  /-- The transition relation. -/
  δ : Set (Q × List A × L × Q)
  /-- There are only finitely many transitions. -/
  δ_finite : δ.Finite

namespace LabAut

variable {A L Q : Type}

/-- A path in the automaton, given as the list of the transitions it uses. -/
inductive Path (M : LabAut A L Q) : Q → List (Q × List A × L × Q) → Q → Prop
  | nil (q : Q) : Path M q [] q
  | cons {q : Q} {u : List A} {l : L} {q' : Q} {ts : List (Q × List A × L × Q)} {p : Q} :
      (q, u, l, q') ∈ M.δ → Path M q' ts p → Path M q ((q, u, l, q') :: ts) p

/-- The input string of a path: the concatenation of the input strings of its
transitions. -/
def inputOf (ts : List (Q × List A × L × Q)) : List A := (ts.map (fun t => t.2.1)).flatten

/-- The labels along a path, in the order of the transitions. -/
def labelsOf (ts : List (Q × List A × L × Q)) : List L := ts.map (fun t => t.2.2.1)

/-- A path is accepting if it starts in an initial state and ends in a final state.
-/
def Accepting (M : LabAut A L Q) (ts : List (Q × List A × L × Q)) : Prop :=
  ∃ q ∈ M.init, ∃ p ∈ M.final, M.Path q ts p

/-- The accepting paths with a given input string. -/
def acceptingOn (M : LabAut A L Q) (w : List A) : Set (List (Q × List A × L × Q)) :=
  {ts | M.Accepting ts ∧ inputOf ts = w}

end LabAut

end Lax132576.LabelledAutomata
end

-- Lax132576.WeightedAutomata
section
namespace Lax132576.WeightedAutomata

open Lax132576.LabelledAutomata

variable {A S Q : Type} [Semiring S]

/-- The weight of a path: the product of the weights of its transitions, in the
order in which they are taken. -/
def weightOf (ts : List (Q × List A × S × Q)) : S := (LabAut.labelsOf ts).prod

/-- The semantics of a weighted automaton: the sum of the weights of the accepting
runs over the input. -/
noncomputable def wEval (M : LabAut A S Q) (w : List A) : S :=
  ∑ᶠ ts ∈ M.acceptingOn w, weightOf ts

end Lax132576.WeightedAutomata
end
