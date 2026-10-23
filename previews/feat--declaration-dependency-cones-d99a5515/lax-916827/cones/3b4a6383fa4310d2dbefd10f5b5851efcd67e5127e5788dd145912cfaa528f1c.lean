-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Computability.DFA
import Mathlib.Data.List.Basic

-- Lax765601.Continuity
section
namespace Lax765601.Continuity

/-- A string-to-string function is *continuous* if the inverse image of every
regular language over the output alphabet is a regular language. -/
def Continuous {A B : Type} (f : List A → List B) : Prop :=
  ∀ L : Language B, L.IsRegular → Language.IsRegular ({w : List A | f w ∈ L} : Language A)

end Lax765601.Continuity
end

-- Lax765601.MapLifting
section
namespace Lax765601.MapLifting

/-- Cut a string over `A + 1` (the separator being `none`) into its maximal blocks
without the separator; there is always one block more than there are separators.
-/
def splitSep {A : Type} : List (Option A) → List (List A)
  | [] => [[]]
  | none :: w => [] :: splitSep w
  | some a :: w =>
      match splitSep w with
      | [] => [[a]]
      | u :: us => (a :: u) :: us

/-- The map lifting of `f`: apply `f` to every block delimited by the separator,
`w₁ # ⋯ # wₙ ↦ f w₁ # ⋯ # f wₙ`. -/
def mapLift {A B : Type} (f : List A → List B) (w : List (Option A)) : List (Option B) :=
  List.intercalate [none] ((splitSep w).map (fun u => (f u).map some))

end Lax765601.MapLifting
end

-- Lax916827.MapLiftingContinuity
section
namespace Lax916827.MapLiftingContinuity

open Lax765601.Continuity Lax765601.MapLifting

/-- The map lifting of a continuous function is continuous. -/
axiom continuous_mapLift {A B : Type} [Finite A] [Finite B] {f : List A → List B}
    (hf : Continuous f) : Continuous (mapLift f)

end Lax916827.MapLiftingContinuity
end
