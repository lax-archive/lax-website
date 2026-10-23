-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Computability.TuringMachine.Computable

-- Lax434930.PolynomialTime
section
namespace Lax434930
end Lax434930

namespace Lax434930.PolynomialTime
end Lax434930.PolynomialTime
end

-- Lax429075.CNF
section
namespace Lax429075.CNF

structure Literal where
  index : ℕ
  positive : Bool
  deriving DecidableEq

abbrev Clause := List Literal

abbrev Formula := List Clause

abbrev Assignment := ℕ → Bool

def Literal.eval (l : Literal) (ρ : Assignment) : Bool :=
  if l.positive then ρ l.index else !(ρ l.index)

def eval (F : Formula) (ρ : Assignment) : Bool :=
  F.all fun C => C.any fun l => l.eval ρ

end Lax429075.CNF
end

-- Lax429075.Circuits
section
namespace Lax429075.Circuits.Circuit
end Lax429075.Circuits.Circuit

namespace Lax429075.Circuits

open CNF

inductive Gate
  | input
  | constant (value : Bool)
  | neg (a : ℕ)
  | conj (a b : ℕ)
  | disj (a b : ℕ)
  deriving DecidableEq

def Gate.inputs : Gate → List ℕ
  | .input | .constant _ => []
  | .neg a => [a]
  | .conj a b | .disj a b => [a, b]

def Gate.check (ρ : Assignment) (i : ℕ) : Gate → Bool
  | .input => true
  | .constant b => ρ i == b
  | .neg a => ρ i == !(ρ a)
  | .conj a b => ρ i == (ρ a && ρ b)
  | .disj a b => ρ i == (ρ a || ρ b)

end Lax429075.Circuits
end

-- Lax429075.Tseitin
section
namespace Lax429075.Tseitin

open CNF Circuits

def positive (i : ℕ) : Literal := ⟨i, true⟩

def negative (i : ℕ) : Literal := ⟨i, false⟩

def gateClauses (i : ℕ) : Gate → Formula
  | .input => []
  | .constant b => [[⟨i, b⟩]]
  | .neg a => [[positive i, positive a], [negative i, negative a]]
  | .conj a b => [[negative i, positive a], [negative i, positive b],
      [positive i, negative a, negative b]]
  | .disj a b => [[positive i, negative a], [positive i, negative b],
      [negative i, positive a, positive b]]

end Lax429075.Tseitin
end

-- Lax429075.GateCorrect
section
namespace Lax429075.GateCorrect

open CNF Circuits Tseitin

axiom correct (i : ℕ) (g : Gate) (ρ : Assignment) :
  eval (gateClauses i g) ρ = g.check ρ i

end Lax429075.GateCorrect
end
