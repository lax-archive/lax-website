-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Computability.TuringMachine.Computable

-- Lax218471.PolynomialTime
section
namespace Lax218471.PolynomialTime

open Turing

/-- A finite machine and a time bound realizing every input/output pair of a contract. -/
structure Implementation {A : Type} (R : List A → List A → Prop) extends
    TM2ComputableAux A A where
  time : Polynomial ℕ
  correct : ∀ x y, R x y →
    Nonempty (TM2OutputsInTime tm (x.map inputAlphabet.symm)
      (some (y.map outputAlphabet.symm)) (time.eval x.length))

end Lax218471.PolynomialTime
end
