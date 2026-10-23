-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic

-- Lax434930.PolynomialTime
section
namespace Lax434930.PolynomialTime

/-- A finite binary string. -/
abbrev Word := List Bool

end Lax434930.PolynomialTime
end

-- Lax689614.ArcKayles
section
namespace Lax689614
end Lax689614

namespace Lax689614.ArcKayles
end Lax689614.ArcKayles

namespace Lax689614.ArcKayles.Winning
end Lax689614.ArcKayles.Winning
end

-- Lax689614.PositiveCNF
section
namespace Lax689614
end Lax689614

namespace Lax689614.PositiveCNF
end Lax689614.PositiveCNF

namespace Lax689614.PositiveCNF.Formula
end Lax689614.PositiveCNF.Formula

namespace Lax689614.PositiveCNF.TrueWins
end Lax689614.PositiveCNF.TrueWins
end

-- Lax689614.Encoding
section
namespace Lax689614.Encoding

open Lax434930.PolynomialTime

structure Graph where
  vertices : ℕ
  graph : SimpleGraph (Fin vertices)

noncomputable def graphWord (G : Graph) : Word := by
  classical
  exact List.replicate G.vertices true ++ [false] ++
    (List.finRange G.vertices).flatMap fun u =>
      (List.finRange G.vertices).map fun v => decide (G.graph.Adj u v)

end Lax689614.Encoding
end

-- Lax689614.Construction
section
namespace Lax689614.Construction
end Lax689614.Construction
end

-- Lax689614.Sizes
section
namespace Lax689614.Sizes

axiom graph_length (G : Encoding.Graph) :
    (Encoding.graphWord G).length = G.vertices ^ 2 + G.vertices + 1

end Lax689614.Sizes
end
