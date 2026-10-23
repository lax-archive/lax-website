-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Computability.TuringMachine.Computable

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

/-- The copy of the variable `v` at position `p`. -/
def wv (V v p : ℕ) : ℕ := v + p * V

/-- The link variable after position `p`. -/
def zv (V N p : ℕ) : ℕ := V * N + p

/-- A placeholder literal, used when an index is past the end of a list. -/
def dflt : Literal := ⟨0, false⟩

/-- The `i`-th clause of the chain of `C`, whose first literal sits at position `o`: the
negated link before it (except for `i = 0`), the copy of the `i`-th literal, and the link
after it (except for the last). -/
def chainClause (V N o : ℕ) (C : Clause) (i : ℕ) : Clause :=
  (if i = 0 then [] else [⟨zv V N (o + i - 1), false⟩]) ++
    [⟨wv V (C.getD i dflt).index (o + i), (C.getD i dflt).positive⟩] ++
    (if i + 1 = C.length then [] else [⟨zv V N (o + i), true⟩])

end Lax345332.Construction
end
