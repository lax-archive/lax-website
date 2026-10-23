-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Computability.DFA
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Set.Finite.Basic

-- Lax314295.MSOLogic
section
namespace Lax314295.MSOLogic.MSO.IsFO
end Lax314295.MSOLogic.MSO.IsFO

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

end MSO

end Lax314295.MSOLogic
end

-- Lax314295.MSOTransductions
section
namespace Lax314295.MSOTransductions

open Lax314295.MSOLogic

/-- A string-to-string mso transduction of the linear type `copies · n + extra`,
presented by families of ordinary mso formulas indexed by the variants of the
type. -/
structure MSOTransduction (A B : Type) where
  /-- The number of copies of the input positions. -/
  copies : ℕ
  /-- The number of extra (constant) elements. -/
  extra : ℕ
  /-- Universe formulas for the copies of the positions; free variable `x₀`. -/
  univP : Fin copies → MSO A
  /-- Universe formulas for the extra elements; sentences. -/
  univC : Fin extra → MSO A
  /-- Letter formulas for the copies of the positions; free variable `x₀`. -/
  labP : Fin copies → B → MSO A
  /-- Letter formulas for the extra elements; sentences. -/
  labC : Fin extra → B → MSO A
  /-- Order formulas between two copies of positions; free variables `x₀, x₁`. -/
  ordPP : Fin copies → Fin copies → MSO A
  /-- Order formulas between a copy of a position and an extra element. -/
  ordPC : Fin copies → Fin extra → MSO A
  /-- Order formulas between an extra element and a copy of a position. -/
  ordCP : Fin extra → Fin copies → MSO A
  /-- Order formulas between two extra elements. -/
  ordCC : Fin extra → Fin extra → MSO A

namespace MSOTransduction

variable {A B : Type}

/-- The elements of the type `copies · n + extra`, before selection. -/
abbrev Elt (T : MSOTransduction A B) : Type := (Fin T.copies × ℕ) ⊕ Fin T.extra

/-- The elements selected by the universe formulas. -/
def selected (T : MSOTransduction A B) (w : List A) : T.Elt → Prop
  | Sum.inl (i, p) => p < w.length ∧ MSO.Sat w (fun _ => p) (fun _ => ∅) (T.univP i)
  | Sum.inr j => MSO.Sat w (fun _ => 0) (fun _ => ∅) (T.univC j)

/-- The order defined by the order formulas. -/
def ordRel (T : MSOTransduction A B) (w : List A) : T.Elt → T.Elt → Prop
  | Sum.inl (i, p), Sum.inl (i', p') =>
      MSO.Sat w (fun v => if v = 0 then p else p') (fun _ => ∅) (T.ordPP i i')
  | Sum.inl (i, p), Sum.inr j => MSO.Sat w (fun _ => p) (fun _ => ∅) (T.ordPC i j)
  | Sum.inr j, Sum.inl (i, p) => MSO.Sat w (fun _ => p) (fun _ => ∅) (T.ordCP j i)
  | Sum.inr j, Sum.inr j' => MSO.Sat w (fun _ => 0) (fun _ => ∅) (T.ordCC j j')

/-- The labelling defined by the letter formulas. -/
def labRel (T : MSOTransduction A B) (w : List A) : T.Elt → B → Prop
  | Sum.inl (i, p), b => MSO.Sat w (fun _ => p) (fun _ => ∅) (T.labP i b)
  | Sum.inr j, b => MSO.Sat w (fun _ => 0) (fun _ => ∅) (T.labC j b)

/-- The transduction outputs `v` on `w`: `v` lists the selected elements, without
repetition, in the order of the order formula, each labelled by a letter of
its letter formulas. -/
def Outputs (T : MSOTransduction A B) (w : List A) (v : List B) : Prop :=
  ∃ es : List T.Elt,
    es.Nodup ∧
    (∀ x, x ∈ es ↔ T.selected w x) ∧
    (∀ (i j : ℕ) (hi : i < es.length) (hj : j < es.length),
      i < j → T.ordRel w (es.get ⟨i, hi⟩) (es.get ⟨j, hj⟩)) ∧
    es.length = v.length ∧
    ∀ (i : ℕ) (hi : i < es.length) (hi' : i < v.length),
      T.labRel w (es.get ⟨i, hi⟩) (v.get ⟨i, hi'⟩)

/-- The requirement of Definition C.4.7: on every input, every selected element
satisfies exactly one letter formula, and the order formula is a linear order
on the selected elements. -/
def Proper (T : MSOTransduction A B) : Prop :=
  ∀ w : List A,
    (∀ x, T.selected w x → ∃! b, T.labRel w x b) ∧
    (∀ x, T.selected w x → T.ordRel w x x) ∧
    (∀ x y, T.selected w x → T.selected w y →
      T.ordRel w x y → T.ordRel w y x → x = y) ∧
    (∀ x y z, T.selected w x → T.selected w y → T.selected w z →
      T.ordRel w x y → T.ordRel w y z → T.ordRel w x z) ∧
    (∀ x y, T.selected w x → T.selected w y → T.ordRel w x y ∨ T.ordRel w y x)

end MSOTransduction

/-- A function defined by a string-to-string mso transduction satisfying the
requirements of the definition. -/
def IsMSOTransduction {A B : Type} (f : List A → List B) : Prop :=
  ∃ T : MSOTransduction A B, T.Proper ∧ ∀ w, T.Outputs w (f w)

end Lax314295.MSOTransductions
end

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

-- Lax765601.CompositionClosure
section
namespace Lax765601.CompositionClosure

/-- A family of string-to-string functions, indexed by the input and the output
alphabet. -/
abbrev Family : Type 1 := ∀ (A B : Type), (List A → List B) → Prop

/-- The closure `P*` of a family `P` under composition: the identity functions, the
members of `P`, and the compositions `g ∘ f` of two members of the closure through
a finite intermediate alphabet. -/
inductive CompClosure (P : Family) : Family
  /-- A prime function belongs to the closure. -/
  | base {A B : Type} {f : List A → List B} : P A B f → CompClosure P A B f
  /-- The identity on every alphabet belongs to the closure. -/
  | protected id (A : Type) : CompClosure P A A _root_.id
  /-- The closure is closed under composition through a finite alphabet. -/
  | comp {A B C : Type} [Finite B] {f : List A → List B} {g : List B → List C} :
      CompClosure P A B f → CompClosure P B C g → CompClosure P A C (g ∘ f)

end Lax765601.CompositionClosure
end

-- Lax765601.MapLifting
section
namespace Lax765601.MapLifting

/-- Cut a string over `A + 1` (the separator being `none`) into its maximal blocks
without the separator; there is always one block more than there are separators.
-/
def splitSep {A : Type} : List (Option A) → List (List A)
  | [] => [[]]
  | none :: w => [] :: splitSep w
  | some a :: w =>
      match splitSep w with
      | [] => [[a]]
      | u :: us => (a :: u) :: us

/-- The map lifting of `f`: apply `f` to every block delimited by the separator,
`w₁ # ⋯ # wₙ ↦ f w₁ # ⋯ # f wₙ`. -/
def mapLift {A B : Type} (f : List A → List B) (w : List (Option A)) : List (Option B) :=
  List.intercalate [none] ((splitSep w).map (fun u => (f u).map some))

end Lax765601.MapLifting
end

-- Lax916827.RegularFunctions
section
namespace Lax916827.RegularFunctions

open Lax765601.MapLifting Lax765601.CompositionClosure Lax132576.RationalFunctions

/-- The map reverse function `w₁ # ⋯ # wₙ ↦ reverse w₁ # ⋯ # reverse wₙ`. -/
def mapReverse (A : Type) : List (Option A) → List (Option A) := mapLift List.reverse

/-- The map duplicate function `w₁ # ⋯ # wₙ ↦ w₁w₁ # ⋯ # wₙwₙ`. -/
def mapDuplicate (A : Type) : List (Option A) → List (Option A) := mapLift (fun w => w ++ w)

/-- The family of prime regular functions: rational functions, and the map reverse
and map duplicate functions, up to a renaming of the alphabets. -/
def RegularFam : Family := fun A B f =>
  IsRationalFun f ∨
  (∃ (A₀ : Type) (e : A ≃ Option A₀) (e' : B ≃ Option A₀),
      ∀ w, f w = (mapReverse A₀ (w.map e)).map e'.symm) ∨
  (∃ (A₀ : Type) (e : A ≃ Option A₀) (e' : B ≃ Option A₀),
      ∀ w, f w = (mapDuplicate A₀ (w.map e)).map e'.symm)

/-- A string-to-string function is regular if it is a finite composition of
rational functions, map reverse and map duplicate. -/
def IsRegularFun {A B : Type} (f : List A → List B) : Prop := CompClosure RegularFam A B f

end Lax916827.RegularFunctions
end

-- Lax314295.MSOTransductionOfRegular
section
namespace Lax314295.MSOTransductionOfRegular

open Lax916827.RegularFunctions Lax314295.MSOTransductions

/-- A regular function is defined by an mso transduction. -/
axiom isMSOTransduction_of_isRegularFun {A B : Type} [Finite A] [Finite B]
    {f : List A → List B} (hf : IsRegularFun f) : IsMSOTransduction f

end Lax314295.MSOTransductionOfRegular
end
