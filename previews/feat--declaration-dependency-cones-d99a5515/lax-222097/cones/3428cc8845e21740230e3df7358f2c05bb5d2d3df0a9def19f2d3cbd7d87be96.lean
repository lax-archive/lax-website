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

end Lax434930.PolynomialTime
end

-- Lax222097.GraphEncoding
section
namespace Lax222097.GraphEncoding.Instance
end Lax222097.GraphEncoding.Instance

namespace Lax222097.GraphEncoding

open scoped Classical

open List Turing Lax434930.PolynomialTime

/-- Encode a natural number as that many one-bits followed by a zero-bit. -/
def unary (n : ℕ) : Word := replicate n true ++ [false]

end Lax222097.GraphEncoding
end
