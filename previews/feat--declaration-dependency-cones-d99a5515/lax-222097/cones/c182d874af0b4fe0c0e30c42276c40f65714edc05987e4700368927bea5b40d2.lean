-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.List.FinRange

-- Lax434930.PolynomialTime
section
namespace Lax434930
end Lax434930

namespace Lax434930.PolynomialTime
end Lax434930.PolynomialTime
end

-- Lax222097.GraphEncoding
section
namespace Lax222097
end Lax222097

namespace Lax222097.GraphEncoding
end Lax222097.GraphEncoding

namespace Lax222097.GraphEncoding.Instance
end Lax222097.GraphEncoding.Instance
end

-- Lax222097.MaxCut
section
namespace Lax222097.MaxCut
end Lax222097.MaxCut
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

-- Lax222097.GraphProblems
section
namespace Lax222097.GraphProblems

open GraphEncoding MaxCut Turing

open Lax434930.PolynomialTime Lax434930.NondeterministicPolynomialTime

abbrev GraphClass := ∀ {n : ℕ}, SimpleGraph (Fin n) → Prop

end Lax222097.GraphProblems
end
