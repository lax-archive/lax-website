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

-- Lax429075.CNF
section
namespace Lax429075.CNF

structure Literal where
  index : ℕ
  positive : Bool
  deriving DecidableEq

end Lax429075.CNF
end

-- Lax429075.Circuits
section
namespace Lax429075.Circuits
end Lax429075.Circuits

namespace Lax429075.Circuits.Circuit
end Lax429075.Circuits.Circuit

namespace Lax429075.Circuits.Gate
end Lax429075.Circuits.Gate

namespace Lax429075.Circuits.Gate.conj
end Lax429075.Circuits.Gate.conj

namespace Lax429075.Circuits.Gate.constant
end Lax429075.Circuits.Gate.constant

namespace Lax429075.Circuits.Gate.disj
end Lax429075.Circuits.Gate.disj

namespace Lax429075.Circuits.Gate.input
end Lax429075.Circuits.Gate.input

namespace Lax429075.Circuits.Gate.inputs
end Lax429075.Circuits.Gate.inputs

namespace Lax429075.Circuits.Gate.neg
end Lax429075.Circuits.Gate.neg
end

-- Lax429075.Tseitin
section
namespace Lax429075.Tseitin.gateClauses
end Lax429075.Tseitin.gateClauses

namespace Lax429075.Tseitin

open CNF Circuits

def positive (i : ℕ) : Literal := ⟨i, true⟩

end Lax429075.Tseitin
end
