-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

-- Lax342547.ContainerRun
section
namespace Lax342547.ContainerRun

noncomputable def next {U : Type} (H : U → U → Prop) (I R : Finset U) (v : U) : Finset U := by
  classical
  exact if v ∈ I then R.filter (fun w => ¬ H v w) else R.erase v

noncomputable def run {U : Type} (active : Finset U → Prop) (pick : Finset U → U)
    (H : U → U → Prop) (I : Finset U) : ℕ → Finset U → Finset U × List U := by
  classical
  exact fun fuel R => match fuel with
  | 0 => (R,[])
  | n+1 => if active R then
      let v := pick R
      let result := run active pick H I n (next H I R v)
      (result.1,if v ∈ I then v::result.2 else result.2)
    else (R,[])

axiom run_preserves {U : Type} (active : Finset U → Prop) (pick : Finset U → U)
    (H : U → U → Prop) (I R : Finset U) (fuel : ℕ)
    (hI : I ⊆ R) (hind : ∀ x ∈ I, ∀ y ∈ I, ¬ H x y) :
    I ⊆ (run active pick H I fuel R).1 ∧ (run active pick H I fuel R).1 ⊆ R

end Lax342547.ContainerRun
end
