-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Tactic.DeriveFintype

-- Lax759944.BinaryWordEncoding
section
set_option backward.isDefEq.respectTransparency false

namespace Lax759944.BinaryWordEncoding

/-- The finite alphabet used to encode lists of natural numbers. -/
inductive Symbol
  | separator
  | zero
  | one
  deriving DecidableEq, Fintype, Inhabited

/-- Encode one natural number, including the separator which begins it. -/
def encodeNat (n : ℕ) : List Symbol :=
  .separator :: n.bits.map (fun b => if b then .one else .zero)

/-- The canonical binary encoding of a finite list of natural numbers. -/
def encode (x : List ℕ) : List Symbol :=
  x.flatMap encodeNat

end Lax759944.BinaryWordEncoding
end

-- Lax759944.TuringPolytime
section
namespace Lax759944.TuringPolytime

open Lax759944.BinaryWordEncoding

/-- Polynomial-time computation, on the canonical binary word encoding, by
a finite multi-tape Turing machine. -/
def TuringPolytime (f : List ℕ → List ℕ) : Prop :=
  Nonempty (Turing.TM2ComputableInPolyTime encode encode f)

end Lax759944.TuringPolytime
end

-- Lax614640.Machine
section
set_option autoImplicit false

namespace Lax614640.Machine

open Lax759944.BinaryWordEncoding Lax759944.TuringPolytime

/-- A finite machine word.  Boolean data use the entries $0$ and $1$. -/
abbrev BitString := List ℕ

/-- The convenient monomial bound $c(n+1)^k$. -/
def polynomialBound (c k n : ℕ) : ℕ :=
  c * (n + 1) ^ k

/-- A total word function computed in polynomial time by a finite Turing machine. -/
structure PolytimeProgram where
  function : BitString → BitString
  polytime : TuringPolytime function

/-- A length-prefixed pairing of two finite words. -/
def pairBits (left right : BitString) : BitString :=
  left.length :: left ++ right

/-- A uniformly random string of exactly $r$ bits. -/
abbrev RandomSeed (r : ℕ) := Fin r → Bool

end Lax614640.Machine
end

-- Lax614640.Complexity
section
namespace Lax614640.Complexity.TriangleFreeMISApproximation
end Lax614640.Complexity.TriangleFreeMISApproximation

set_option autoImplicit false

namespace Lax614640.Complexity

open Lax614640.Machine

export Lax614640.Machine
  (BitString RandomSeed PolytimeProgram polynomialBound pairBits)

/-- An executable simple graph on the labeled vertex set $\operatorname{Fin}(n)$. -/
structure GraphCode (n : ℕ) where
  adjacent : Fin n → Fin n → Bool
  loopless : ∀ vertex, adjacent vertex vertex = false
  symmetric : ∀ left right, adjacent left right = adjacent right left

end Lax614640.Complexity
end
