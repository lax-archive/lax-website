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

/-- The input/output relation of an encoded function. -/
def Graph {α β A : Type} (ea : α → List A) (eb : β → List A) (f : α → β)
    (x y : List A) : Prop := ∃ a, ea a = x ∧ eb (f a) = y

end Lax218471.PolynomialTime
end
