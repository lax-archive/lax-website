-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.List.Basic
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

-- Lax765601.Aperiodicity
section
namespace Lax765601.Aperiodicity

/-- The `n`-fold concatenation `vⁿ` of a string with itself. -/
def npow {A : Type} (v : List A) : ℕ → List A
  | 0 => []
  | n + 1 => v ++ npow v n

end Lax765601.Aperiodicity
end

-- Lax314295.KTypesAperiodicity
section
namespace Lax314295.KTypesAperiodicity

open Lax765601.Aperiodicity Lax314295.KTypes

/-- The `k`-types of the powers of a string eventually stabilise. -/
axiom exists_tp_npow_eq {A : Type} (k : ℕ) (w : List A) :
    ∃ N : ℕ, ∀ n ≥ N, tp k (npow w n) = tp k (npow w N)

end Lax314295.KTypesAperiodicity
end
