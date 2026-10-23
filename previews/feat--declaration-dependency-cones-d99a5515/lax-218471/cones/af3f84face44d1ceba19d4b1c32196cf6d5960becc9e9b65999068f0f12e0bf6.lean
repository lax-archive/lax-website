-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Computability.TuringMachine.Computable

-- Lax218471.PolynomialTime
section
namespace Lax218471.PolynomialTime

open Turing

/-- Existence of a finite machine computing an encoded function in polynomial time. -/
def Polytime {α β A B : Type} (ea : α → List A) (eb : β → List B) (f : α → β) : Prop :=
  Nonempty (TM2ComputableInPolyTime ea eb f)

/-- A finite machine and a time bound realizing every input/output pair of a contract. -/
structure Implementation {A : Type} (R : List A → List A → Prop) extends
    TM2ComputableAux A A where
  time : Polynomial ℕ
  correct : ∀ x y, R x y →
    Nonempty (TM2OutputsInTime tm (x.map inputAlphabet.symm)
      (some (y.map outputAlphabet.symm)) (time.eval x.length))

/-- The input/output relation of an encoded function. -/
def Graph {α β A : Type} (ea : α → List A) (eb : β → List A) (f : α → β)
    (x y : List A) : Prop := ∃ a, ea a = x ∧ eb (f a) = y

end Lax218471.PolynomialTime
end

-- Lax218471.Combinators
section
namespace Lax218471.Combinators

open PolynomialTime

/-- An existential polynomial-time algorithm realizes its encoded contract. -/
axiom graph_realizable {α β A : Type} {ea : α → List A} {eb : β → List A} {f : α → β}
    (h : Polytime ea eb f) : Nonempty (Implementation (Graph ea eb f))

end Lax218471.Combinators
end
