-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Logic.Basic
import Mathlib.ModelTheory.Semantics

-- Lax904597.Problems
section
namespace Lax904597
end Lax904597

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax904597.Problems.DecisionProblem
end Lax904597.Problems.DecisionProblem
end

-- Lax485149.Problems
section
namespace Lax485149
end Lax485149

namespace Lax485149.Problems
end Lax485149.Problems

namespace Lax485149.Problems.DecisionProblem
end Lax485149.Problems.DecisionProblem

namespace Lax485149.Problems.DecisionProblem.ofPred
end Lax485149.Problems.DecisionProblem.ofPred
end

-- Lax604544.RelationIsomorphism
section
namespace Lax604544.RelationIsomorphism

section Generic

variable {A : Type}

/-- Some map is a bijection of the `PV`-vertices onto the `HV`-vertices
carrying `PE`-edges to `HE`-edges *and back*: an isomorphism of the two marked
graphs. -/
def RelIsoOn (PV HV : A → Prop) (PE HE : A → A → Prop) : Prop :=
  ∃ f : A → A, (∀ x, PV x → HV (f x)) ∧
    (∀ x y, PV x → PV y → f x = f y → x = y) ∧
    (∀ y, HV y → ∃ x, PV x ∧ f x = y) ∧
    ∀ x y, PV x → PV y → (PE x y ↔ HE (f x) (f y))

end Generic

end Lax604544.RelationIsomorphism
end

-- Lax604544.DagIsomorphism
section
namespace Lax604544.DagIsomorphism

open Lax904597.Problems Lax485149.Problems Lax604544.RelationIsomorphism

open FirstOrder

open FirstOrder.Language

/-- The relation symbols of the language. -/
inductive twoDagsRel : ℕ → Type where
/-- `patV a`: `a` is a vertex of the pattern DAG. -/
  | patV : twoDagsRel 1
/-- `hostV a`: `a` is a vertex of the host DAG. -/
  | hostV : twoDagsRel 1
/-- `patArc a b`: there is an arc of the pattern DAG from `a` to `b`. -/
  | patArc : twoDagsRel 2
/-- `hostArc a b`: there is an arc of the host DAG from `a` to `b`. -/
  | hostArc : twoDagsRel 2
/-- `patLt a b`: `a` precedes `b` in the pattern's topological order. -/
  | patLt : twoDagsRel 2
/-- `hostLt a b`: `a` precedes `b` in the host's topological order. -/
  | hostLt : twoDagsRel 2
  deriving DecidableEq

/-- The relational language of two directed acyclic graphs: two arc relations
sharing a universe, each with its own vertex mark and its own topological
order. -/
def twoDags : FirstOrder.Language :=
  ⟨fun _ => Empty, twoDagsRel⟩

/-- `patV a`: `a` is a vertex of the pattern DAG. -/
abbrev tdPatV : twoDags.Relations 1 :=
  .patV

/-- `hostV a`: `a` is a vertex of the host DAG. -/
abbrev tdHostV : twoDags.Relations 1 :=
  .hostV

/-- `patArc a b`: there is an arc of the pattern DAG from `a` to `b`. -/
abbrev tdPatArc : twoDags.Relations 2 :=
  .patArc

/-- `hostArc a b`: there is an arc of the host DAG from `a` to `b`. -/
abbrev tdHostArc : twoDags.Relations 2 :=
  .hostArc

/-- `patLt a b`: `a` precedes `b` in the pattern's topological order. -/
abbrev tdPatLt : twoDags.Relations 2 :=
  .patLt

/-- `hostLt a b`: `a` precedes `b` in the host's topological order. -/
abbrev tdHostLt : twoDags.Relations 2 :=
  .hostLt

open FirstOrder

open Language Structure

section Topo

variable {A : Type}

/-- `Lt` is a topological order for the arcs `Arc` on the marked set `V`: a
strict partial order (on `V`) containing the arcs. Its existence is exactly the
acyclicity of the arcs, and it is first-order checkable, which acyclicity
itself is not. -/
def TopoOn (V : A → Prop) (Lt Arc : A → A → Prop) : Prop :=
  (∀ x, V x → ¬Lt x x) ∧
    (∀ x y z, V x → V y → V z → Lt x y → Lt y z → Lt x z) ∧
    ∀ x y, V x → V y → Arc x y → Lt x y

end Topo

section Shorthands

variable {A : Type} [twoDags.Structure A]

/-- `patV a`: `a` is a vertex of the pattern DAG.  -/
def TDPatV {A : Type} [twoDags.Structure A] (a0 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap tdPatV ![a0]

/-- `hostV a`: `a` is a vertex of the host DAG.  -/
def TDHostV {A : Type} [twoDags.Structure A] (a0 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap tdHostV ![a0]

/-- `patArc a b`: there is an arc of the pattern DAG from `a` to `b`.  -/
def TDPatArc {A : Type} [twoDags.Structure A] (a0 : A) (a1 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap tdPatArc ![a0, a1]

/-- `hostArc a b`: there is an arc of the host DAG from `a` to `b`.  -/
def TDHostArc {A : Type} [twoDags.Structure A] (a0 : A) (a1 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap tdHostArc ![a0, a1]

/-- `patLt a b`: `a` precedes `b` in the pattern's topological order.  -/
def TDPatLt {A : Type} [twoDags.Structure A] (a0 : A) (a1 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap tdPatLt ![a0, a1]

/-- `hostLt a b`: `a` precedes `b` in the host's topological order.  -/
def TDHostLt {A : Type} [twoDags.Structure A] (a0 : A) (a1 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap tdHostLt ![a0, a1]

end Shorthands

section Problem

variable (A : Type) [twoDags.Structure A]

/-- Both sides are well-formed – each order relation is a topological order of
its arcs, so both marked arc relations are acyclic – and the two DAGs are
isomorphic. The isomorphism relates the arcs only: the two orders are the
instance's acyclicity witnesses, not part of the structure being matched. -/
def HasDagIso : Prop :=
  Finite A ∧ TopoOn (TDPatV (A := A)) TDPatLt TDPatArc ∧
    TopoOn (TDHostV (A := A)) TDHostLt TDHostArc ∧
    RelIsoOn (TDPatV (A := A)) TDHostV TDPatArc TDHostArc

end Problem

end Lax604544.DagIsomorphism
end
