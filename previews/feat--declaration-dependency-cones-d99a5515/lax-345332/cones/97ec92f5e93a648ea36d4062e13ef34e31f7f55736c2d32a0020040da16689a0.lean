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

/-- Tovey's thirteen clauses on the variables `g, g+1, …, g+9`; they force `g` to be true. -/
def gadget (g : ℕ) : Formula :=
  let y := g
  let a (j : ℕ) := g + 1 + 3 * j
  let b (j : ℕ) := g + 2 + 3 * j
  let d (j : ℕ) := g + 3 + 3 * j
  ((List.range 3).map fun j => [⟨y, true⟩, ⟨a j, true⟩, ⟨b j, true⟩]) ++
  ((List.range 3).flatMap fun j =>
    [[⟨d j, true⟩, ⟨a j, true⟩, ⟨b j, false⟩], [⟨d j, true⟩, ⟨a j, false⟩, ⟨b j, true⟩],
     [⟨d j, true⟩, ⟨a j, false⟩, ⟨b j, false⟩]]) ++
  [[⟨d 0, false⟩, ⟨d 1, false⟩, ⟨d 2, false⟩]]

/-- The base of the `t`-th gadget of the `k`-th clause, above the variables below `B`. -/
def ybase (B k t : ℕ) : ℕ := B + 30 * k + 10 * t

/-- The padding literals of a clause of length `n`. -/
def pads (B k n : ℕ) : Clause := (List.range (3 - n)).map fun t => ⟨ybase B k t, false⟩

/-- The `k`-th clause, padded, with its three gadgets. -/
def unit (B k : ℕ) (C : Clause) : Formula :=
  (C ++ pads B k C.length) ::
    (gadget (ybase B k 0) ++ gadget (ybase B k 1) ++ gadget (ybase B k 2))

/-- Every clause of `G`, padded to three literals and followed by its gadgets. `B` bounds the
variables in use. -/
def pad (B : ℕ) (G : Formula) : Formula :=
  (List.range G.length).flatMap fun k => unit B k (G.getD k [])

end Lax345332.Construction
end
