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
namespace Lax429075.CNF.Literal
end Lax429075.CNF.Literal

namespace Lax429075.CNF

abbrev Assignment := ℕ → Bool

end Lax429075.CNF
end

-- Lax429075.Circuits
section
namespace Lax429075.Circuits.Circuit
end Lax429075.Circuits.Circuit

namespace Lax429075.Circuits

open CNF

inductive Gate
  | input
  | constant (value : Bool)
  | neg (a : ℕ)
  | conj (a b : ℕ)
  | disj (a b : ℕ)
  deriving DecidableEq

def Gate.inputs : Gate → List ℕ
  | .input | .constant _ => []
  | .neg a => [a]
  | .conj a b | .disj a b => [a, b]

def Gate.check (ρ : Assignment) (i : ℕ) : Gate → Bool
  | .input => true
  | .constant b => ρ i == b
  | .neg a => ρ i == !(ρ a)
  | .conj a b => ρ i == (ρ a && ρ b)
  | .disj a b => ρ i == (ρ a || ρ b)

end Lax429075.Circuits
end
