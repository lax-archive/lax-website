-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Clique

-- Lax342547.SampledGraph
section
namespace Lax342547.SampledGraph

universe u

def sampleGraph {Ω : Type u} (hole : Ω → Ω → Prop) (hsymm : (∀ ⦃i j⦄, hole i j → hole j i))
    {m : ℕ} (sample : Fin m → Ω) : SimpleGraph (Fin m) where
  Adj i j := i ≠ j ∧ ¬ hole (sample i) (sample j)
  symm := ⟨fun _ _ h ↦ ⟨h.1.symm, fun h' ↦ h.2 (hsymm h')⟩⟩
  loopless := ⟨fun _ h ↦ h.1 rfl⟩

axiom sampleGraph_indepNum_le_two {Ω : Type u}
    (hole : Ω → Ω → Prop) (hsymm : (∀ ⦃i j⦄, hole i j → hole j i))
    (htriangle : ∀ i j k, hole i j → hole j k → ¬ hole k i)
    {m : ℕ} (sample : Fin m → Ω) :
    (sampleGraph hole hsymm sample).indepNum ≤ 2

end Lax342547.SampledGraph
end
