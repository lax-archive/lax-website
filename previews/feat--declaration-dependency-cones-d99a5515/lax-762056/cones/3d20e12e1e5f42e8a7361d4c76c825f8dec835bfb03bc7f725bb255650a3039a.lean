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

-- Lax762056.GraphEncoding
section
namespace Lax762056.GraphEncoding

open List Turing Lax434930.PolynomialTime

structure Instance where
  order : ℕ
  graph : SimpleGraph (Fin order)
  threshold : ℕ

end Lax762056.GraphEncoding
end

-- Lax762056.MaxCut
section
namespace Lax762056.MaxCut
end Lax762056.MaxCut
end

-- Lax762056.GraphProblems
section
namespace Lax762056.GraphProblems

open GraphEncoding MaxCut Turing

open Lax434930.PolynomialTime Lax434930.NondeterministicPolynomialTime

def IndependentSet (I : Instance) : Prop := I.threshold ≤ I.graph.indepNum

end Lax762056.GraphProblems
end
