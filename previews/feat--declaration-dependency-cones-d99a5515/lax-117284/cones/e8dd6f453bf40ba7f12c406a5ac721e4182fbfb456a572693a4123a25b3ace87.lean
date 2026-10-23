-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.Finset.Card
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
namespace Lax117284
end Lax117284

namespace Lax117284.TwoSatCNF
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

/-- **Reachability** in the implication graph, by a path of any length including zero. -/
def Reaches (F : Formula) : Literal → Literal → Prop := Relation.ReflTransGen (Implies F)

/-- **A contradictory variable**: it reaches its negation, and its negation reaches it. -/
def Contradictory (F : Formula) (x : ℕ) : Prop :=
  Reaches F (pos x) (neg x) ∧ Reaches F (neg x) (pos x)

end Lax117284.TwoSatImplicationGraph
end
