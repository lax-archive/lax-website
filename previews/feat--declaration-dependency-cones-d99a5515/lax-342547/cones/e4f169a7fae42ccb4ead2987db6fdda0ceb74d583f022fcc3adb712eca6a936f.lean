-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Pi

-- Lax342547.RestrictionRank
section
namespace Lax342547
end Lax342547

namespace Lax342547.RestrictionRank
end Lax342547.RestrictionRank
end

-- Lax342547.DirectRanks
section
namespace Lax342547.DirectRanks

open scoped BigOperators

noncomputable def rangeProductEquiv {K ι : Type} [Field K]
    {V W : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (M : ∀ i, V i →ₗ[K] W i) :
    LinearMap.range (LinearMap.piMap M) ≃ₗ[K] (∀ i, LinearMap.range (M i)) := by
  classical
  let f : LinearMap.range (LinearMap.piMap M) →ₗ[K] (∀ i, LinearMap.range (M i)) :=
    { toFun := fun w i => ⟨w.val i,by obtain ⟨v,hv⟩ := w.property; exact ⟨v i,congrFun hv i⟩⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  refine LinearEquiv.ofBijective f ?_
  constructor
  · intro w z h
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val (congrFun h i)
  · intro w
    have hex : ∀ i, ∃ v, M i v = (w i).val := fun i => (w i).property
    choose v hv using hex
    refine ⟨⟨fun i => (w i).val,⟨v,?_⟩⟩,?_⟩
    · funext i
      exact hv i
    · rfl

end Lax342547.DirectRanks
end
