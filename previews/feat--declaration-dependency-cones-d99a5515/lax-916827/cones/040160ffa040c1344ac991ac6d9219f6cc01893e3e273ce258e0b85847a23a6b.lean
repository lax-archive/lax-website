-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Finite.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Set.Card
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

-- Lax916827.SnakeGraphs
section
namespace Lax916827.SnakeGraphs

/-- The alphabet `C` of snake letters for the state set `Q` and output alphabet `B`:
a letter gives, for every vertex of the two copies of `Q`, its outgoing edge to
the other copy with a label in `B + 1`, if any. -/
abbrev SnakeLetter (Q B : Type) := Bool × Q → Option (Q × Option B)

/-- A vertex of a snake graph: a row `q` and a column `i`. -/
abbrev Vtx (Q : Type) := Q × ℕ

/-- The edge relation of the graph represented by `w`: an edge from `v` to `v'`
labelled `o` is recorded by the letter between their columns, read from the left
copy when `v'` is in the next column and from the right copy when it is in the
previous one. -/
def Edge {Q B : Type} (w : List (SnakeLetter Q B)) (v v' : Vtx Q) (o : Option B) : Prop :=
  (v'.2 = v.2 + 1 ∧ ∃ c, w[v.2]? = some c ∧ c (false, v.1) = some (v'.1, o)) ∨
  (v.2 = v'.2 + 1 ∧ ∃ c, w[v'.2]? = some c ∧ c (true, v.1) = some (v'.1, o))

/-- The vertex `v` carries an edge, incoming or outgoing. -/
def Incident {Q B : Type} (w : List (SnakeLetter Q B)) (v : Vtx Q) : Prop :=
  (∃ v' o, Edge w v v' o) ∨ (∃ u o, Edge w u v o)

/-- All edges of the graph represented by `w` lie on the single directed path
`p 0, …, p m` with pairwise distinct vertices and edge labels `lab`: this is
what makes the graph a snake graph. -/
structure IsSnakePath {Q B : Type} (w : List (SnakeLetter Q B)) (m : ℕ) (p : ℕ → Vtx Q)
    (lab : ℕ → Option B) : Prop where
  /-- Consecutive vertices of the path are joined by an edge with the recorded
  label. -/
  edge : ∀ t < m, Edge w (p t) (p (t + 1)) (lab t)
  /-- The vertices of the path are pairwise distinct. -/
  inj : ∀ s ≤ m, ∀ t ≤ m, p s = p t → s = t
  /-- Every edge of the graph is an edge of the path. -/
  covers : ∀ v v' o, Edge w v v' o → ∃ t < m, p t = v ∧ p (t + 1) = v' ∧ lab t = o

/-- The output along a path: the concatenation of the labels of its edges, the
label `none` contributing nothing. -/
def pathOut {B : Type} (lab : ℕ → Option B) (m : ℕ) : List B :=
  ((List.range m).map (fun t => (lab t).toList)).flatten

/-- `v` is the output of the snake graph represented by `w`. -/
def SnakeOutIs {Q B : Type} (w : List (SnakeLetter Q B)) (v : List B) : Prop :=
  ∃ m p lab, IsSnakePath w m p lab ∧ v = pathOut lab m

/-- The number of times the snake visits the column `i`: the number of vertices of
that column carrying an edge. -/
noncomputable def colVisits {Q B : Type} (w : List (SnakeLetter Q B)) (i : ℕ) : ℕ :=
  {q : Q | Incident w (q, i)}.ncard

/-- The width of the represented graph is at most `k`. -/
def SnakeWidthLe {Q B : Type} (w : List (SnakeLetter Q B)) (k : ℕ) : Prop :=
  ∀ i, colVisits w i ≤ k

open Classical in
/-- The function of the snake lemma: the output of the snake graph represented by
`w`, if `w` represents one of width at most `k`, and the empty string otherwise.
-/
noncomputable def snakeOut {Q B : Type} (k : ℕ) (w : List (SnakeLetter Q B)) : List B :=
  if h : SnakeWidthLe w k ∧ ∃ v, SnakeOutIs w v then h.2.choose else []

end Lax916827.SnakeGraphs
end

-- Lax916827.SnakeLemma
section
namespace Lax916827.SnakeLemma

open Lax916827.RegularFunctions Lax916827.SnakeGraphs

/-- The output of a snake graph of width at most `k`, read off its string
representation, is a regular function. -/
axiom isRegularFun_snakeOut {Q B : Type} [Finite Q] [Finite B] (k : ℕ) :
    IsRegularFun (snakeOut (Q := Q) (B := B) k)

end Lax916827.SnakeLemma
end
