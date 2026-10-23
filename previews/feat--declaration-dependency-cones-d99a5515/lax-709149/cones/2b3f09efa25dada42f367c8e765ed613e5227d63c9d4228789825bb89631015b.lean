-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic.DeriveFintype

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

-- Lax709149.RegularTerms
section
namespace Lax709149.RegularTerms

open Lax709149.Types

/-- The prefix products of a list: the `i`-th entry of the output is the product of
the first `i` entries of the input. -/
def prefixProd {M : Type} [Monoid M] (l : List M) : List M := (l.scanl (· * ·) 1).tail

/-- Split: the input is cut at its entries from `B`; the output is the block of
entries from `A` before the first cut, and the cutting entries each with the block
that follows it. -/
def splitList {A B : Type} : List (A ⊕ B) → List A × List (B × List A)
  | [] => ([], [])
  | Sum.inl a :: l => ((splitList l).1.cons a, (splitList l).2)
  | Sum.inr b :: l => ([], (b, (splitList l).1) :: (splitList l).2)

/-- The syntax of regular terms: atomic terms and combinators. -/
inductive RegTerm : Ty → Ty → Type
  /-- Identity `A → A`. -/
  | id (A : Ty) : RegTerm A A
  /-- First projection `A × B → A`. -/
  | fst (A B : Ty) : RegTerm (.prod A B) A
  /-- Second projection `A × B → B`. -/
  | snd (A B : Ty) : RegTerm (.prod A B) B
  /-- Left co-projection `A → A + B`. -/
  | inl (A B : Ty) : RegTerm A (.sum A B)
  /-- Right co-projection `B → A + B`. -/
  | inr (A B : Ty) : RegTerm B (.sum A B)
  /-- Distributivity `A × (B + C) → (A × B) + (A × C)`. -/
  | distr (A B C : Ty) : RegTerm (.prod A (.sum B C)) (.sum (.prod A B) (.prod A C))
  /-- The list constructor `1 + A × A* → A*`. -/
  | cons (A : Ty) : RegTerm (.sum .one (.prod A (.list A))) (.list A)
  /-- The list deconstructor `A* → 1 + A × A*`. -/
  | uncons (A : Ty) : RegTerm (.list A) (.sum .one (.prod A (.list A)))
  /-- Reverse `A* → A*`. -/
  | reverse (A : Ty) : RegTerm (.list A) (.list A)
  /-- Concatenation `A** → A*`. -/
  | concat (A : Ty) : RegTerm (.list (.list A)) (.list A)
  /-- Split `(A + B)* → A* × (B × A*)*`. -/
  | split (A B : Ty) : RegTerm (.list (.sum A B)) (.prod (.list A) (.list (.prod B (.list A))))
  /-- Group prefix multiplication `G* → G*`, for a group on a finite type. -/
  | pref (G : Ty) (grp : Group G.Elt) (hfin : Finite G.Elt) : RegTerm (.list G) (.list G)
  /-- Composition. -/
  | comp {A B C : Ty} : RegTerm A B → RegTerm B C → RegTerm A C
  /-- Pairing. -/
  | pair {A B C : Ty} : RegTerm A B → RegTerm A C → RegTerm A (.prod B C)
  /-- Co-pairing. -/
  | copair {A B C : Ty} : RegTerm A C → RegTerm B C → RegTerm (.sum A B) C
  /-- Map. -/
  | map {A B : Ty} : RegTerm A B → RegTerm (.list A) (.list B)

/-- The function defined by a regular term. -/
def RegTerm.eval : {A B : Ty} → RegTerm A B → A.Elt → B.Elt
  | _, _, .id _ => fun x => x
  | _, _, .fst _ _ => fun x => x.1
  | _, _, .snd _ _ => fun x => x.2
  | _, _, .inl _ _ => fun x => Sum.inl x
  | _, _, .inr _ _ => fun x => Sum.inr x
  | _, _, .distr _ _ _ => fun x =>
      Sum.elim (fun b => Sum.inl (x.1, b)) (fun c => Sum.inr (x.1, c)) x.2
  | _, _, .cons _ => fun x => Sum.elim (fun _ => []) (fun p => p.1 :: p.2) x
  | _, _, .uncons _ => fun l => match l with
      | [] => Sum.inl ()
      | a :: l' => Sum.inr (a, l')
  | _, _, .reverse _ => fun l => l.reverse
  | _, _, .concat _ => fun l => l.flatten
  | _, _, .split _ _ => fun l => splitList l
  | _, _, .pref _ grp _ => fun l => @prefixProd _ (@Group.toDivisionMonoid _ grp).toMonoid l
  | _, _, .comp s t => fun x => t.eval (s.eval x)
  | _, _, .pair s t => fun x => (s.eval x, t.eval x)
  | _, _, .copair s t => fun x => Sum.elim s.eval t.eval x
  | _, _, .map t => fun l => l.map t.eval

/-- A type-to-type function is defined by a regular term. -/
def IsRegularTermFun {A B : Ty} (f : A.Elt → B.Elt) : Prop := ∃ t : RegTerm A B, t.eval = f

end Lax709149.RegularTerms
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

-- Lax709149.RegularUnderRepresentation
section
namespace Lax709149.RegularUnderRepresentation

open Lax132576.RationalFunctions Lax916827.RegularFunctions Lax709149.Types

/-- A type-to-type function is regular under string representation if a regular
string-to-string function maps the representation of `a` to the representation
of `f a`. -/
def IsRegularUnderRepr {A B : Ty} (f : A.Elt → B.Elt) : Prop :=
  ∃ f' : List Sym8 → List Sym8, IsRegularFun f' ∧ ∀ a : A.Elt, f' (A.repr a) = B.repr (f a)

end Lax709149.RegularUnderRepresentation
end

-- Lax709149.RegularOfTerm
section
namespace Lax709149.RegularOfTerm

open Lax709149.Types Lax709149.RegularUnderRepresentation Lax709149.RegularTerms

/-- A function defined by a regular term is regular under string representation. -/
axiom isRegularUnderRepr_of_isRegularTermFun {A B : Ty} {f : A.Elt → B.Elt}
    (hf : IsRegularTermFun f) : IsRegularUnderRepr f

end Lax709149.RegularOfTerm
end
