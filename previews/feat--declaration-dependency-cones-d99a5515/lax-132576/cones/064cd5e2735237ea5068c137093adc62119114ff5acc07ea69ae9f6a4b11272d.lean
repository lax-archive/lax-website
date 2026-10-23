-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Computability.Halting
import Mathlib.Data.Rat.Defs
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

-- Lax132576.RationalRelations
section
namespace Lax132576.RationalRelations
end Lax132576.RationalRelations

namespace Lax132576.RationalRelations.NFAO
end Lax132576.RationalRelations.NFAO
end

-- Lax132576.TransducerCodes
section
namespace Lax132576.TransducerCodes.RelCode
end Lax132576.TransducerCodes.RelCode

namespace Lax132576.TransducerCodes

open Lax132576.LabelledAutomata Lax132576.RationalRelations

/-- A property `P` is decidable under a promise if a computable Boolean-valued
function answers `P` correctly on every input satisfying the promise. -/
def DecidableUnderPromise {α : Type} [Primcodable α] (promise P : α → Prop) : Prop :=
  ∃ D : α → Bool, Computable D ∧ ∀ a, promise a → (D a = true ↔ P a)

end Lax132576.TransducerCodes
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

/-- The requirement of Definition B.3.2: every input string has only finitely
many accepting runs. -/
def FinitelyManyRuns (M : LabAut A S Q) : Prop := ∀ w : List A, (M.acceptingOn w).Finite

end Lax132576.WeightedAutomata
end

-- Lax132576.WeightedCodes
section
namespace Lax132576.WeightedCodes

open Lax132576.LabelledAutomata Lax132576.WeightedAutomata

/-- A code of a weighted automaton over `ℚ`: transitions `(p, u, (a, b), q)` from
`p` to `q` reading `u` with weight `a / b`, and the initial and final states. -/
structure WCode where
  /-- The transitions `(p, u, (a, b), q)`. -/
  transitions : List (ℕ × List ℕ × (ℤ × ℕ) × ℕ)
  /-- The initial states. -/
  init : List ℕ
  /-- The final states. -/
  final : List ℕ

/-- A code is the tuple of its three lists. -/
def wcodeEquiv : WCode ≃ List (ℕ × List ℕ × (ℤ × ℕ) × ℕ) × List ℕ × List ℕ where
  toFun c := (c.transitions, c.init, c.final)
  invFun x := ⟨x.1, x.2.1, x.2.2⟩
  left_inv := by rintro ⟨t, i, f⟩; rfl
  right_inv := by rintro ⟨t, i, f⟩; rfl

instance : Primcodable WCode := Primcodable.ofEquiv _ wcodeEquiv

/-- The weighted automaton over `ℚ` described by a code. -/
def wcodeAut (c : WCode) : LabAut ℕ ℚ ℕ where
  init := {q | q ∈ c.init}
  final := {q | q ∈ c.final}
  δ := {t | ∃ s ∈ c.transitions, t = (s.1, s.2.1, (s.2.2.1.1 : ℚ) / (s.2.2.1.2 : ℚ), s.2.2.2)}
  δ_finite := Set.Finite.ofFinset
    (c.transitions.toFinset.image
      (fun s => (s.1, s.2.1, (s.2.2.1.1 : ℚ) / (s.2.2.1.2 : ℚ), s.2.2.2)))
    (by intro t; simp [eq_comm])

/-- The function computed by the weighted automaton described by a code. -/
noncomputable def wcodeEval (c : WCode) : List ℕ → ℚ := wEval (wcodeAut c)

/-- A code is valid if it describes a genuine weighted automaton: every input has
finitely many accepting runs. -/
def WCodeValid (c : WCode) : Prop := FinitelyManyRuns (wcodeAut c)

end Lax132576.WeightedCodes
end

-- Lax132576.WeightedEquivalenceDecidable
section
namespace Lax132576.WeightedEquivalenceDecidable

open Lax132576.TransducerCodes Lax132576.WeightedCodes

/-- Equivalence of two valid coded weighted automata over `ℚ` is decidable. -/
axiom decidable_wcodeEval_eq :
    DecidableUnderPromise (fun p : WCode × WCode => WCodeValid p.1 ∧ WCodeValid p.2)
      (fun p => wcodeEval p.1 = wcodeEval p.2)

end Lax132576.WeightedEquivalenceDecidable
end
