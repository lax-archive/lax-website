-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.List.FinRange

-- Lax434930.PolynomialTime
section
namespace Lax434930.PolynomialTime

/-- A finite binary string. -/
abbrev Word := List Bool

/-- A language of finite binary strings. -/
abbrev Language := Set Word

/-- Languages whose Boolean characteristic functions are computable in polynomial time. -/
def P : Set Language :=
  {L | ∃ f : Word → Bool,
    (∀ w, f w = true ↔ w ∈ L) ∧
    Nonempty (Turing.TM2ComputableInPolyTime id Computability.encodeBool f)}

end Lax434930.PolynomialTime
end

-- Lax434930.Certificates
section
namespace Lax434930.Certificates.unpair
end Lax434930.Certificates.unpair

namespace Lax434930.Certificates

open PolynomialTime

/-- A self-delimiting encoding of the first string, followed by the second. -/
def pair : Word → Word → Word
  | [], y => true :: y
  | b :: x, y => false :: b :: pair x y

end Lax434930.Certificates
end

-- Lax434930.NondeterministicPolynomialTime
section
namespace Lax434930.NondeterministicPolynomialTime

open PolynomialTime Certificates

/-- Languages with polynomially bounded, polynomial-time verifiable certificates. -/
def NP : Set Language :=
  {A | ∃ V : Language, V ∈ P ∧ ∃ p : Polynomial ℕ, ∀ x : Word,
    x ∈ A ↔ ∃ y : Word, y.length ≤ p.eval x.length ∧ pair x y ∈ V}

end Lax434930.NondeterministicPolynomialTime
end

-- Lax762056.GraphEncoding
section
namespace Lax762056.GraphEncoding

open List Turing Lax434930.PolynomialTime

structure Instance where
  order : ℕ
  graph : SimpleGraph (Fin order)
  threshold : ℕ

def unary (n : ℕ) : Word := replicate n true ++ [false]

noncomputable def encode (I : Instance) : Word := by
  classical
  exact unary I.order ++
    (finRange I.order).flatMap (fun u =>
      (finRange I.order).map (fun v => decide (I.graph.Adj u v))) ++
    unary I.threshold

end Lax762056.GraphEncoding
end

-- Lax762056.MaxCut
section
namespace Lax762056.MaxCut
end Lax762056.MaxCut
end

-- Lax762056.GraphProblems
section
namespace Lax762056.GraphProblems

open GraphEncoding MaxCut Turing

open Lax434930.PolynomialTime Lax434930.NondeterministicPolynomialTime

abbrev GraphClass := ∀ {n : ℕ}, SimpleGraph (Fin n) → Prop

abbrev DecisionProblem := Instance → Prop

def NPHardOn (problem : DecisionProblem) (graphs : GraphClass) : Prop :=
  ∀ A : Language, A ∈ NP →
    ∃ f : Word → Instance,
      Nonempty (TM2ComputableInPolyTime id encode f) ∧
      ∀ x, graphs (f x).graph ∧ (x ∈ A ↔ problem (f x))

end Lax762056.GraphProblems
end
