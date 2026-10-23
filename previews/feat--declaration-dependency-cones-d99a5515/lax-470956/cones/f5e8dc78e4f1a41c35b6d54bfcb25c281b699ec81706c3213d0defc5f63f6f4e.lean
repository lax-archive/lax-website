-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.List.FinRange
import Mathlib.Data.Nat.Bits

-- Lax434930.PolynomialTime
section
namespace Lax434930.PolynomialTime

/-- A finite binary string. -/
abbrev Word := List Bool

end Lax434930.PolynomialTime
end

-- Lax470956.Scheduling
section
namespace Lax470956
end Lax470956

namespace Lax470956.Scheduling
end Lax470956.Scheduling

namespace Lax470956.Scheduling.Instance
end Lax470956.Scheduling.Instance
end

-- Lax470956.BinaryEncoding
section
namespace Lax470956.BinaryEncoding

open Lax470956.Scheduling Lax434930.PolynomialTime

/-- A natural number as a binary word: its digits, least significant first, preceded by
their number in unary. The unary prefix makes the code self-delimiting. -/
def encodeNat (n : ℕ) : Word :=
  List.replicate n.bits.length true ++ [false] ++ n.bits

end Lax470956.BinaryEncoding
end
