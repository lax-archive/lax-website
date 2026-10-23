-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

-- Lax342547.ContainerRun
section
namespace Lax342547.ContainerRun.run
end Lax342547.ContainerRun.run

namespace Lax342547.ContainerRun

noncomputable def next {U : Type} (H : U → U → Prop) (I R : Finset U) (v : U) : Finset U := by
  classical
  exact if v ∈ I then R.filter (fun w => ¬ H v w) else R.erase v

axiom next_card_lt {U : Type} (H : U → U → Prop) (I R : Finset U) (v : U)
    (hv : v ∈ R) (hne : ∃ w ∈ R, H v w) : (next H I R v).card < R.card

end Lax342547.ContainerRun
end
