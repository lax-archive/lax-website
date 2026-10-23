-- Lax dependency cone
-- Lean: v4.30.0
-- Mathlib: c5ea00351c28e24afc9f0f84379aa41082b1188f

import Mathlib.Data.Fintype.Basic
import Mathlib.ModelTheory.Semantics

-- Lax52.MSOSyntax
section
namespace Lax52.MSOSyntax

open FirstOrder

universe u v

/-- Monadic second-order formulas over `L`, intrinsically scoped by the numbers
of available first-order and monadic variables. -/
inductive Formula (L : Language.{u, v}) : Nat → Nat → Type (max u v)
  | falsum {n m : Nat} : Formula L n m
  | equal {n m : Nat} : L.Term (Fin n) → L.Term (Fin n) → Formula L n m
  | rel {n m k : Nat} : L.Relations k → (Fin k → L.Term (Fin n)) → Formula L n m
  | mem {n m : Nat} : L.Term (Fin n) → Fin m → Formula L n m
  | or {n m : Nat} : Formula L n m → Formula L n m → Formula L n m
  | neg {n m : Nat} : Formula L n m → Formula L n m
  | exFO {n m : Nat} : Formula L (n + 1) m → Formula L n m
  | exSO {n m : Nat} : Formula L n (m + 1) → Formula L n m

/-- An MSO sentence has no free variables of either sort. -/
abbrev Sentence (L : Language.{u, v}) := Formula L 0 0

namespace Formula

variable {L : Language.{u, v}} {n m : Nat}

end Formula

end Lax52.MSOSyntax
end

-- Lax53.RankedTree
section
namespace Lax53.RankedTree

universe u

/-- A finite alphabet whose symbols have prescribed arities. -/
structure RankedAlphabet where
  Symbol : Type u
  [symbolsFintype : Fintype Symbol]
  [symbolsDecidableEq : DecidableEq Symbol]
  rank : Symbol → Nat

attribute [instance] RankedAlphabet.symbolsFintype

attribute [instance] RankedAlphabet.symbolsDecidableEq

/-- Finite terms over a ranked alphabet. A node labelled by `a` has one
ordered child for each element of `Fin (A.rank a)`. -/
inductive Tree (A : RankedAlphabet.{u}) : Type u
  | node (a : A.Symbol) (children : Fin (A.rank a) → Tree A) : Tree A

/-- The set of child slots occurring in the alphabet. Its zero-based index
`i` represents the slot customarily numbered `i+1`. -/
def ChildIndex (A : RankedAlphabet.{u}) : Type :=
  {i : Nat // ∃ a : A.Symbol, i < A.rank a}

namespace ChildIndex

/-- Regard a child slot of a particular symbol as a child slot of the whole
alphabet. -/
def ofSymbolIndex {A : RankedAlphabet.{u}} (a : A.Symbol)
    (i : Fin (A.rank a)) : ChildIndex A :=
  ⟨i, ⟨a, i.isLt⟩⟩

end ChildIndex

/-- The nodes occurring in a particular ranked tree. -/
inductive Node {A : RankedAlphabet.{u}} : Tree A → Type u
  | root {a : A.Symbol} {children : Fin (A.rank a) → Tree A} :
      Node (.node a children)
  | inChild {a : A.Symbol} {children : Fin (A.rank a) → Tree A}
      (i : Fin (A.rank a)) (p : Node (children i)) :
      Node (.node a children)

namespace Node

/-- The root node of a tree. -/
def rootOf {A : RankedAlphabet.{u}} : (t : Tree A) → Node t
  | .node _ _ => .root

/-- The symbol labelling a node. -/
def label {A : RankedAlphabet.{u}} : {t : Tree A} → Node t → A.Symbol
  | .node a _, .root => a
  | .node _ _, .inChild _ p => label p

/-- The `i`th child of a node, as a node of the same ambient tree. -/
def child {A : RankedAlphabet.{u}} :
    {t : Tree A} → (p : Node t) → Fin (A.rank p.label) → Node t
  | .node _ children, .root, i => .inChild i (rootOf (children i))
  | .node _ _, .inChild j p, i => .inChild j (child p i)

/-- `ChildAt i p q` says that `q` is the immediate child of `p` in the
alphabet-wide child slot `i`. -/
def ChildAt {A : RankedAlphabet.{u}} (i : ChildIndex A) {t : Tree A}
    (p q : Node t) : Prop :=
  ∃ j : Fin (A.rank p.label),
    ChildIndex.ofSymbolIndex p.label j = i ∧ q = child p j

end Node

/-- A language of ranked trees. -/
abbrev TreeLanguage (A : RankedAlphabet.{u}) := Set (Tree A)

end Lax53.RankedTree
end

-- Lax53.TreeAutomaton
section
namespace Lax53.TreeAutomaton

open Lax53.RankedTree

universe u v

/-- A bottom-up tree automaton with state type `Q`. This basic structure allows
arbitrary state types; recognizable languages and the main theorems explicitly
require finitely many states. -/
structure Automaton (A : RankedAlphabet.{u}) (Q : Type v) where
  transition : (a : A.Symbol) → Q → (Fin (A.rank a) → Q) → Bool
  accept : Q → Bool

namespace Automaton

/-- A run of `M` on `t` leading to state `q`. -/
def RunsTo {A : RankedAlphabet.{u}} {Q : Type v} (M : Automaton A Q) :
    Tree A → Q → Prop
  | .node a children, q =>
      ∃ childStates : Fin (A.rank a) → Q,
        M.transition a q childStates = true ∧
          ∀ i : Fin (A.rank a), M.RunsTo (children i) (childStates i)

/-- A tree is accepted if some run leads to an accepting state. -/
def Accepts {A : RankedAlphabet.{u}} {Q : Type v} (M : Automaton A Q)
    (t : Tree A) : Prop :=
  ∃ q : Q, M.accept q = true ∧ M.RunsTo t q

/-- The language accepted by a tree automaton. -/
def language {A : RankedAlphabet.{u}} {Q : Type v} (M : Automaton A Q) :
    TreeLanguage A :=
  {t | M.Accepts t}

end Automaton

/-- Recognizability by a tree automaton with finitely many states. -/
def Recognizable {A : RankedAlphabet.{u}} (L : TreeLanguage A) : Prop :=
  ∃ Q : Type, ∃ _ : Fintype Q, ∃ M : Automaton A Q, M.language = L

end Lax53.TreeAutomaton
end

-- Lax52.MSOSemantics
section
namespace Lax52.MSOSemantics

open FirstOrder

open FirstOrder.Language

open FirstOrder.Language.Structure

open Lax52.MSOSyntax

universe u v w

variable {L : Language.{u, v}} {M : Type w} [L.Structure M]

/-- Extend a valuation by putting a newly bound variable at index zero. -/
def consVal {n : Nat} (x : M) (v : Fin n → M) : Fin (n + 1) → M :=
  Fin.cases x v

/-- Satisfaction of an MSO formula under first-order and monadic valuations. -/
def Realize : {n m : Nat} → Formula L n m → (Fin n → M) →
    (Fin m → Set M) → Prop
  | _, _, .falsum, _, _ => False
  | _, _, .equal t₁ t₂, v, _ => t₁.realize v = t₂.realize v
  | _, _, .rel r ts, v, _ => RelMap r (fun i => (ts i).realize v)
  | _, _, .mem t X, v, V => t.realize v ∈ V X
  | _, _, .or phi psi, v, V => Realize phi v V ∨ Realize psi v V
  | _, _, .neg phi, v, V => ¬Realize phi v V
  | _, _, .exFO phi, v, V => ∃ x : M, Realize phi (consVal x v) V
  | _, _, .exSO phi, v, V => ∃ X : Set M, Realize phi v (consVal X V)

end Lax52.MSOSemantics
end

-- Lax53.TreeStructure
section
namespace Lax53.TreeStructure

open FirstOrder

open FirstOrder.Language

open Lax53.RankedTree

universe u

/-- Relation symbols for ranked trees. -/
inductive TreeRelation (A : RankedAlphabet.{u}) : Nat → Type u
  | label (a : A.Symbol) : TreeRelation A 1
  | child (i : ChildIndex A) : TreeRelation A 2

/-- The first-order language of ranked trees over `A`. -/
def treeSignature (A : RankedAlphabet.{u}) : FirstOrder.Language.{0, u} where
  Functions := fun _ => Empty
  Relations := TreeRelation A

/-- The canonical first-order structure of a ranked tree. -/
@[implicit_reducible]
def treeStructure {A : RankedAlphabet.{u}} (t : Tree A) :
    (treeSignature A).Structure (Node t) where
  funMap f := nomatch f
  RelMap
    | .label a, xs => Node.label (xs 0) = a
    | .child i, xs => Node.ChildAt i (xs 0) (xs 1)

/-- Satisfaction of a closed MSO sentence by the canonical structure of a
ranked tree. -/
def TreeModels {A : RankedAlphabet.{u}} (t : Tree A)
    (phi : Lax52.MSOSyntax.Sentence (treeSignature A)) : Prop :=
  @Lax52.MSOSemantics.Realize (treeSignature A) (Node t) (treeStructure t) 0 0 phi
    (fun i : Fin 0 => Fin.elim0 i) (fun i : Fin 0 => Fin.elim0 i)

/-- The ranked-tree language defined by an MSO sentence. -/
def sentenceLanguage {A : RankedAlphabet.{u}}
    (phi : Lax52.MSOSyntax.Sentence (treeSignature A)) : TreeLanguage A :=
  {t | TreeModels t phi}

end Lax53.TreeStructure
end

-- Lax53.MSOTreeAutomataEquivalence
section
namespace Lax53.MSOTreeAutomataEquivalence

open Lax53.RankedTree

open Lax53.TreeStructure

open Lax53.TreeAutomaton

universe u v

/-- Recognizability and MSO definability characterize the same languages. -/
axiom recognizable_iff_msoDefinable {A : RankedAlphabet.{u}}
    (L : TreeLanguage A) :
  Recognizable L ↔
    ∃ phi : Lax52.MSOSyntax.Sentence (treeSignature A), L = sentenceLanguage phi

end Lax53.MSOTreeAutomataEquivalence
end
