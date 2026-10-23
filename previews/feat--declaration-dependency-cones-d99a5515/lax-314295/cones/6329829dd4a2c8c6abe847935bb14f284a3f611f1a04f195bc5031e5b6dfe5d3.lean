-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Set.Basic

-- Lax314295.KTypes
section
namespace Lax314295.KTypes

/-- The type of `k`-types over the alphabet `A`. -/
def TpType (A : Type) : ℕ → Type
  | 0 => Unit
  | k + 1 => Set (TpType A k × A × TpType A k)

/-- The `k`-type of a string: trivial for `k = 0`, and for `k + 1` the set of
triples `(tp k w₁, a, tp k w₂)` over the factorisations `w = w₁ a w₂`. -/
def tp {A : Type} : (k : ℕ) → List A → TpType A k
  | 0, _ => ()
  | k + 1, w =>
      {t : TpType A k × A × TpType A k |
        ∃ (w₁ : List A) (a : A) (w₂ : List A), w = w₁ ++ a :: w₂ ∧ t = (tp k w₁, a, tp k w₂)}

end Lax314295.KTypes
end

-- Lax314295.KTypesRefinement
section
namespace Lax314295.KTypesRefinement

open Lax314295.KTypes

/-- Equal `(k+1)`-types have equal `k`-types. -/
axiom tp_eq_of_tp_succ_eq {A : Type} (k : ℕ) (w v : List A) (h : tp (k + 1) w = tp (k + 1) v) :
    tp k w = tp k v

end Lax314295.KTypesRefinement
end
