-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Computability.TuringMachine.Computable

-- Lax434930.PolynomialTime
section
namespace Lax434930.PolynomialTime

/-- A finite binary string. -/
abbrev Word := List Bool

end Lax434930.PolynomialTime
end

-- Lax434930.Certificates
section
namespace Lax434930.Certificates.pair
end Lax434930.Certificates.pair

namespace Lax434930.Certificates

open PolynomialTime

/-- Decode a pair, rejecting a missing delimiter or an incomplete bit block. -/
def unpair : Word → Option (Word × Word)
  | [] => none
  | true :: y => some ([], y)
  | false :: [] => none
  | false :: b :: rest => (unpair rest).map (fun p => (b :: p.1, p.2))

end Lax434930.Certificates
end
