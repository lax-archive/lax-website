-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Group.Even
import Mathlib.Data.Finset.Card

-- Lax712553.Involution
section
namespace Lax712553.Involution

/-- A finite set carrying a fixed-point-free involution has even cardinality. -/
axiom even_card_of_fixedPointFree_involution {α : Type*} [DecidableEq α]
    (S : Finset α) (f : α → α) (hmaps : ∀ x ∈ S, f x ∈ S) (hinv : ∀ x ∈ S, f (f x) = x)
    (hfree : ∀ x ∈ S, f x ≠ x) : Even S.card

end Lax712553.Involution
end
