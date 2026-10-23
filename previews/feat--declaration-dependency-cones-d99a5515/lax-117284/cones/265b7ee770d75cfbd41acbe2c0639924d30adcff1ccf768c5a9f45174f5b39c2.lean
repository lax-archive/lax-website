-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Logic.Relation

-- Lax434930.PolynomialTime
section
namespace Lax434930
end Lax434930

namespace Lax434930.PolynomialTime
end Lax434930.PolynomialTime
end

-- Lax429075.CNF
section
namespace Lax429075.CNF

structure Literal where
  index : ℕ
  positive : Bool
  deriving DecidableEq

abbrev Clause := List Literal

abbrev Formula := List Clause

abbrev Assignment := ℕ → Bool

def Literal.eval (l : Literal) (ρ : Assignment) : Bool :=
  if l.positive then ρ l.index else !(ρ l.index)

def eval (F : Formula) (ρ : Assignment) : Bool :=
  F.all fun C => C.any fun l => l.eval ρ

def Satisfiable (F : Formula) : Prop := ∃ ρ, eval F ρ = true

end Lax429075.CNF
end

-- Lax429075.Encoding
section
namespace Lax429075.Encoding
end Lax429075.Encoding

namespace Lax429075.Encoding.decodeCNF
end Lax429075.Encoding.decodeCNF

namespace Lax429075.Encoding.encodeList
end Lax429075.Encoding.encodeList

namespace Lax429075.Encoding.parseList
end Lax429075.Encoding.parseList

namespace Lax429075.Encoding.parseLiteral
end Lax429075.Encoding.parseLiteral

namespace Lax429075.Encoding.parseNat
end Lax429075.Encoding.parseNat
end

-- Lax434930.Certificates
section
namespace Lax434930.Certificates
end Lax434930.Certificates

namespace Lax434930.Certificates.pair
end Lax434930.Certificates.pair

namespace Lax434930.Certificates.unpair
end Lax434930.Certificates.unpair
end

-- Lax429075.Satisfiability
section
namespace Lax429075.Satisfiability
end Lax429075.Satisfiability
end

-- Lax117284.TwoSatCNF
section
namespace Lax117284.TwoSatCNF

open Lax429075.CNF Lax429075.Encoding Lax429075.Satisfiability Lax434930.PolynomialTime

/-- A CNF formula is in **2-CNF** when every clause has at most two literals. -/
def IsTwoCNF (F : Formula) : Prop := ∀ C ∈ F, C.length ≤ 2

/-- The literals of a formula, in order of occurrence. -/
def literals (F : Formula) : List Literal := F.flatMap id

end Lax117284.TwoSatCNF
end

-- Lax117284.TwoSatImplicationGraph
section
namespace Lax117284.TwoSatImplicationGraph

open Lax429075.CNF

/-- The negation of a literal: the same variable, the opposite sign. -/
def negate (l : Literal) : Literal := ⟨l.index, !l.positive⟩

/-- The positive literal of the variable `x`. -/
def pos (x : ℕ) : Literal := ⟨x, true⟩

/-- The negative literal of the variable `x`. -/
def neg (x : ℕ) : Literal := ⟨x, false⟩

/-- **The edges of the implication graph**: `a → b` when some clause is `[b]` with `a = ¬b`, or
some clause is `[¬a, b]` or `[b, ¬a]`. -/
def Implies (F : Formula) (a b : Literal) : Prop :=
  ∃ C ∈ F, (C = [b] ∧ a = negate b) ∨ C = [negate a, b] ∨ C = [b, negate a]

end Lax117284.TwoSatImplicationGraph
end

-- Lax117284.TwoSatAlgorithm
section
namespace Lax117284.TwoSatAlgorithm

open Lax429075.CNF Lax117284.TwoSatCNF Lax117284.TwoSatImplicationGraph

/-- One more than the largest variable index occurring in `F`, and `0` for no literal. -/
def indexBound (F : Formula) : ℕ := (literals F).foldr (fun l n => max (l.index + 1) n) 0

/-- The nodes of the graph the algorithm searches: the literals with index below the bound. -/
def nodes (F : Formula) : Finset Literal :=
  (Finset.range (indexBound F) ×ˢ (Finset.univ : Finset Bool)).image fun p => ⟨p.1, p.2⟩

instance (F : Formula) : DecidableRel (Implies F) := by
  unfold Implies; infer_instance

/-- The successors of a literal among the nodes. -/
def successors (F : Formula) (a : Literal) : Finset Literal :=
  (nodes F).filter fun b => Implies F a b

/-- One round of the search: add the successors of every literal in the set. -/
def expand (F : Formula) (S : Finset Literal) : Finset Literal := S ∪ S.biUnion (successors F)

/-- **The literals reachable from `s`**: the set the breadth-first search from `s` marks, here
as the result of as many rounds of expansion as there are nodes. -/
def reachable (F : Formula) (s : Literal) : Finset Literal := (expand F)^[(nodes F).card] {s}

/-- Every clause has one or two literals. -/
def widthOk (F : Formula) : Bool := F.all fun C => 1 ≤ C.length && C.length ≤ 2

/-- The variable `x` is found contradictory: its negation is reachable from it, and it from its
negation. -/
def contradictory (F : Formula) (x : ℕ) : Bool :=
  neg x ∈ reachable F (pos x) && pos x ∈ reachable F (neg x)

/-- **The algorithm.** Reject unless every clause has one or two literals; then reject exactly
when some occurring variable is contradictory. -/
def decide (F : Formula) : Bool :=
  widthOk F && ((literals F).map Literal.index).dedup.all fun x => !contradictory F x

end Lax117284.TwoSatAlgorithm
end

-- Lax117284.TwoSatCorrectness
section
namespace Lax117284.TwoSatCorrectness

open Lax429075.CNF Lax117284.TwoSatCNF Lax117284.TwoSatAlgorithm

/-- **The algorithm is correct.** -/
axiom decide_iff (F : Formula) : decide F = true ↔ IsTwoCNF F ∧ Satisfiable F

end Lax117284.TwoSatCorrectness
end
