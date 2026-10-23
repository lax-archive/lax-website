-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Computability.TuringMachine.Computable

-- Lax218471.PolynomialTime
section
namespace Lax218471.PolynomialTime.Implementation
end Lax218471.PolynomialTime.Implementation

namespace Lax218471.PolynomialTime

open Turing

/-- Existence of a finite machine computing an encoded function in polynomial time. -/
def Polytime {α β A B : Type} (ea : α → List A) (eb : β → List B) (f : α → β) : Prop :=
  Nonempty (TM2ComputableInPolyTime ea eb f)

end Lax218471.PolynomialTime
end
