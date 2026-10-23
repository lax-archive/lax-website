-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.List.FinRange
import Mathlib.Data.Nat.Bits

-- Lax434930.PolynomialTime
section
namespace Lax434930
end Lax434930

namespace Lax434930.PolynomialTime
end Lax434930.PolynomialTime
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

-- Lax434930.NondeterministicPolynomialTime
section
namespace Lax434930.NondeterministicPolynomialTime
end Lax434930.NondeterministicPolynomialTime
end

-- Lax429075.Reductions
section
namespace Lax429075
end Lax429075

namespace Lax429075.Reductions
end Lax429075.Reductions
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

-- Lax429075.Satisfiability
section
namespace Lax429075.Satisfiability
end Lax429075.Satisfiability
end

-- Lax345332.ThreeFourSat
section
namespace Lax345332
end Lax345332

namespace Lax345332.ThreeFourSat
end Lax345332.ThreeFourSat
end

-- Lax345332.Construction
section
namespace Lax345332.Construction.bound
end Lax345332.Construction.bound

namespace Lax345332.Construction.chains
end Lax345332.Construction.chains

namespace Lax345332.Construction

open Lax429075.CNF Lax429075.Encoding Lax434930.PolynomialTime Lax345332.ThreeFourSat

/-- A placeholder literal, used when an index is past the end of a list. -/
def dflt : Literal := ⟨0, false⟩

end Lax345332.Construction
end

-- Lax345332.TwoThreeSat
section
namespace Lax345332.TwoThreeSat
end Lax345332.TwoThreeSat

namespace Lax345332.TwoThreeSat.Formula
end Lax345332.TwoThreeSat.Formula
end

-- Lax345332.Copies
section
namespace Lax345332.Copies

open Lax429075.CNF Lax345332.Construction Lax345332.TwoThreeSat Lax434930.PolynomialTime

/-- The literal at position `p` of the flattened formula, and a default literal past its
end. -/
def litAt (F : Lax429075.CNF.Formula) (p : ℕ) : Literal := (F.flatMap id).getD p dflt

end Lax345332.Copies
end
