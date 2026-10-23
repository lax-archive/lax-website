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

/-- The literals of a formula, in order of occurrence. -/
def literals (F : Formula) : List Literal := F.flatMap id

end Lax117284.TwoSatCNF
end

-- Lax117284.TwoSatImplicationGraph
section
namespace Lax117284.TwoSatImplicationGraph
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

end Lax117284.TwoSatAlgorithm
end
