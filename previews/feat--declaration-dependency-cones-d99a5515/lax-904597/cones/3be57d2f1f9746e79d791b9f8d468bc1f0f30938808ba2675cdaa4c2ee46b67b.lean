-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.ModelTheory.Semantics

-- Lax904597.Problems
section
namespace Lax904597.Problems

open FirstOrder FirstOrder.Language

/-- A decision problem: an isomorphism-closed property of `L`-structures,
whose yes-instances are the `L`-structures satisfying it. -/
structure DecisionProblem (L : Language.{0, 0}) [L.IsRelational] where
  /-- The predicate: `P A` (through the function coercion) states that the
  structure `A` is a yes-instance. -/
  Holds : ∀ (A : Type) [L.Structure A], Prop
  /-- Decision problems do not distinguish isomorphic structures. -/
  iso_invariant : ∀ {A B : Type} [L.Structure A] [L.Structure B],
    (A ≃[L] B) → (Holds A ↔ Holds B)

namespace DecisionProblem

variable {L : Language.{0, 0}} [L.IsRelational]

end DecisionProblem

end Lax904597.Problems
end

-- Lax904597.Sat
section
namespace Lax904597.Sat

open FirstOrder FirstOrder.Language FirstOrder.Language.Structure Lax904597.Problems

/-- The relation symbols of CNF instances. -/
inductive satRel : ℕ → Type where
  /-- `isClause c`: the element `c` is a clause. -/
  | isClause : satRel 1
  /-- `posIn c x`: the variable `x` occurs positively in the clause `c`. -/
  | posIn : satRel 2
  /-- `negIn c x`: the variable `x` occurs negatively in the clause `c`. -/
  | negIn : satRel 2
  deriving DecidableEq

/-- The relational language of CNF instances: a unary predicate singling out
clauses, and two binary predicates for positive and negative occurrences of a
variable in a clause. -/
def sat : Language :=
  ⟨fun _ => Empty, satRel⟩

instance instIsRelationalSat : IsRelational sat := fun _ => (inferInstance : IsEmpty Empty)

/-- `isClause c`: the element `c` is a clause. -/
abbrev satIsClause : sat.Relations 1 := .isClause

/-- `posIn c x`: the variable `x` occurs positively in the clause `c`. -/
abbrev satPosIn : sat.Relations 2 := .posIn

/-- `negIn c x`: the variable `x` occurs negatively in the clause `c`. -/
abbrev satNegIn : sat.Relations 2 := .negIn

/-- A CNF instance is satisfiable if some assignment of truth values to its
elements makes every clause contain a true literal. -/
def Satisfiable (A : Type) [sat.Structure A] : Prop :=
  ∃ ν : A → Prop, ∀ c : A, RelMap satIsClause ![c] →
    ∃ x : A, (RelMap satPosIn ![c, x] ∧ ν x) ∨ (RelMap satNegIn ![c, x] ∧ ¬ν x)

/-- SAT: is the CNF instance satisfiable? Invariance transports the
assignment along the isomorphism, atom by atom. -/
def SAT : DecisionProblem sat where
  Holds := fun A inst => @Satisfiable A inst
  iso_invariant := fun {A B} _ _ e => by
    have rel₁ : ∀ {A B : Type} [sat.Structure A] [sat.Structure B] (e : A ≃[sat] B)
        (r : sat.Relations 1) (a : A), RelMap r ![a] ↔ RelMap r ![e a] := by
      intro A B _ _ e r a
      have h := StrongHomClass.map_rel e r ![a]
      have hv : e ∘ ![a] = ![e a] := funext fun i => Fin.cases rfl (fun j => j.elim0) i
      rw [hv] at h
      exact h.symm
    have rel₂ : ∀ {A B : Type} [sat.Structure A] [sat.Structure B] (e : A ≃[sat] B)
        (r : sat.Relations 2) (a b : A), RelMap r ![a, b] ↔ RelMap r ![e a, e b] := by
      intro A B _ _ e r a b
      have h := StrongHomClass.map_rel e r ![a, b]
      have hv : e ∘ ![a, b] = ![e a, e b] :=
        funext fun i => Fin.cases rfl (fun j => Fin.cases rfl (fun j => j.elim0) j) i
      rw [hv] at h
      exact h.symm
    have fwd : ∀ {A B : Type} [sat.Structure A] [sat.Structure B] (e : A ≃[sat] B),
        Satisfiable A → Satisfiable B := by
      intro A B _ _ e hA
      obtain ⟨ν, hν⟩ := hA
      refine ⟨fun b => ν (e.symm b), fun c hc => ?_⟩
      obtain ⟨x, hx⟩ := hν (e.symm c) ((rel₁ e.symm satIsClause c).mp hc)
      refine ⟨e x, ?_⟩
      exact hx.elim
        (fun hp => Or.inl ⟨by simpa using (rel₂ e satPosIn (e.symm c) x).mp hp.1,
          by simpa using hp.2⟩)
        (fun hn => Or.inr ⟨by simpa using (rel₂ e satNegIn (e.symm c) x).mp hn.1,
          by simpa using hn.2⟩)
    exact ⟨fwd e, fwd e.symm⟩

end Lax904597.Sat
end
