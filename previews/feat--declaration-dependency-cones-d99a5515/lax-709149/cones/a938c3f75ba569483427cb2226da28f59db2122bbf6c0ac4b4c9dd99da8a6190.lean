-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Finite.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic.DeriveFintype

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

end LabAut

end Lax132576.LabelledAutomata
end

-- Lax132576.RationalRelations
section
namespace Lax132576.RationalRelations

open Lax132576.LabelledAutomata

/-- A nondeterministic automaton with output: a labelled automaton whose labels
are output strings. -/
abbrev NFAO (A B Q : Type) := LabAut A (List B) Q

namespace NFAO

variable {A B Q : Type}

/-- The output string of a path: the concatenation of the outputs of its
transitions. -/
def outputOf (ts : List (Q × List A × List B × Q)) : List B := (LabAut.labelsOf ts).flatten

/-- The relation computed by an automaton with output: `w` is related to `v` if
some accepting run reads `w` and writes `v`. -/
def rel (M : NFAO A B Q) (w : List A) (v : List B) : Prop :=
  ∃ ts, M.Accepting ts ∧ LabAut.inputOf ts = w ∧ outputOf ts = v

end NFAO

/-- A relation is rational if it is computed by a nondeterministic automaton with
output with a finite state space. -/
def IsRationalRel {A B : Type} (R : List A → List B → Prop) : Prop :=
  ∃ (Q : Type) (_ : Finite Q) (M : NFAO A B Q), ∀ w v, R w v ↔ M.rel w v

end Lax132576.RationalRelations
end

-- Lax132576.RationalFunctions
section
namespace Lax132576.RationalFunctions

open Lax132576.RationalRelations

/-- A string-to-string function is rational if its graph is a rational relation.
-/
def IsRationalFun {A B : Type} (f : List A → List B) : Prop :=
  IsRationalRel (fun w v => v = f w)

end Lax132576.RationalFunctions
end

-- Lax709149.Types
section
namespace Lax709149.Types

/-- A type: built from the unit type by product, co-product and list. -/
inductive Ty : Type
  | one : Ty
  | prod : Ty → Ty → Ty
  | sum : Ty → Ty → Ty
  | list : Ty → Ty
  deriving DecidableEq

/-- The set of elements of a type. -/
def Ty.Elt : Ty → Type
  | .one => Unit
  | .prod A B => A.Elt × B.Elt
  | .sum A B => A.Elt ⊕ B.Elt
  | .list A => List A.Elt

/-- The alphabet with eight letters `(`, `)`, `[`, `]`, `,`, `1`, `L`, `R`. -/
inductive Sym8 : Type
  | lpar | rpar | lbrack | rbrack | comma | one | left | right
  deriving DecidableEq

/-- The entries of a list representation, separated by commas. -/
def joinSep : List (List Sym8) → List Sym8
  | [] => []
  | [x] => x
  | x :: xs => x ++ Sym8.comma :: joinSep xs

/-- The string representation of an element: `1` for the unit, `L a` and `R b` for
the co-product, `(a,b)` for a pair, `[a₁,…,aₙ]` for a list. -/
def Ty.repr : (t : Ty) → t.Elt → List Sym8
  | .one, _ => [Sym8.one]
  | .prod A B, x => Sym8.lpar :: (A.repr x.1 ++ Sym8.comma :: (B.repr x.2 ++ [Sym8.rpar]))
  | .sum A B, x => Sum.elim (fun a => Sym8.left :: A.repr a) (fun b => Sym8.right :: B.repr b) x
  | .list A, l => Sym8.lbrack :: (joinSep (l.map A.repr) ++ [Sym8.rbrack])

end Lax709149.Types
end

-- Lax765601.CompositionClosure
section
namespace Lax765601
end Lax765601

namespace Lax765601.CompositionClosure
end Lax765601.CompositionClosure

namespace Lax765601.CompositionClosure.CompClosure
end Lax765601.CompositionClosure.CompClosure
end

-- Lax765601.MapLifting
section
namespace Lax765601
end Lax765601

namespace Lax765601.MapLifting
end Lax765601.MapLifting

namespace Lax765601.MapLifting.splitSep
end Lax765601.MapLifting.splitSep
end

-- Lax916827.RegularFunctions
section
namespace Lax916827
end Lax916827

namespace Lax916827.RegularFunctions
end Lax916827.RegularFunctions
end

-- Lax709149.RegularUnderRepresentation
section
namespace Lax709149.RegularUnderRepresentation

open Lax132576.RationalFunctions Lax916827.RegularFunctions Lax709149.Types

/-- A type-to-type function is rational under string representation. -/
def IsRationalUnderRepr {A B : Ty} (f : A.Elt → B.Elt) : Prop :=
  ∃ f' : List Sym8 → List Sym8, IsRationalFun f' ∧ ∀ a : A.Elt, f' (A.repr a) = B.repr (f a)

end Lax709149.RegularUnderRepresentation
end
