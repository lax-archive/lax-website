-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

-- Lax342547.ChromaticBound
section
namespace Lax342547.ChromaticBound

axiom card_le_twice_chromaticNumber_of_indepNum
    {V : Type*} [Fintype V] (G : SimpleGraph V) (hα : G.indepNum ≤ 2) :
    Fintype.card V ≤ 2 * G.chromaticNumber.toNat

end Lax342547.ChromaticBound
end
