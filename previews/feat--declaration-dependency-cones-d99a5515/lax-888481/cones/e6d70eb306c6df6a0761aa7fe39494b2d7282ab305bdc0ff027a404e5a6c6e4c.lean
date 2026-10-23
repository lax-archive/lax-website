-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.List.FinRange
import Mathlib.Data.Nat.Bits

-- Lax434930.PolynomialTime
section
namespace Lax434930.PolynomialTime

/-- A finite binary string. -/
abbrev Word := List Bool

/-- A language of finite binary strings. -/
abbrev Language := Set Word

/-- Languages whose Boolean characteristic functions are computable in polynomial time. -/
def P : Set Language :=
  {L | ∃ f : Word → Bool,
    (∀ w, f w = true ↔ w ∈ L) ∧
    Nonempty (Turing.TM2ComputableInPolyTime id Computability.encodeBool f)}

end Lax434930.PolynomialTime
end

-- Lax434930.Certificates
section
namespace Lax434930.Certificates.unpair
end Lax434930.Certificates.unpair

namespace Lax434930.Certificates

open PolynomialTime

/-- A self-delimiting encoding of the first string, followed by the second. -/
def pair : Word → Word → Word
  | [], y => true :: y
  | b :: x, y => false :: b :: pair x y

end Lax434930.Certificates
end

-- Lax434930.NondeterministicPolynomialTime
section
namespace Lax434930.NondeterministicPolynomialTime

open PolynomialTime Certificates

/-- Languages with polynomially bounded, polynomial-time verifiable certificates. -/
def NP : Set Language :=
  {A | ∃ V : Language, V ∈ P ∧ ∃ p : Polynomial ℕ, ∀ x : Word,
    x ∈ A ↔ ∃ y : Word, y.length ≤ p.eval x.length ∧ pair x y ∈ V}

end Lax434930.NondeterministicPolynomialTime
end

-- Lax429075.Reductions
section
namespace Lax429075.Reductions

open Lax434930.PolynomialTime Lax434930.NondeterministicPolynomialTime

def ManyOne (A B : Language) : Prop :=
  ∃ f : Word → Word, Nonempty (Turing.TM2ComputableInPolyTime id id f) ∧
    ∀ x, x ∈ A ↔ f x ∈ B

end Lax429075.Reductions
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

def Satisfiable (F : Formula) : Prop := ∃ ρ, eval F ρ = true

end Lax429075.CNF
end

-- Lax429075.Encoding
section
namespace Lax429075.Encoding.decodeCNF
end Lax429075.Encoding.decodeCNF

namespace Lax429075.Encoding.parseList
end Lax429075.Encoding.parseList

namespace Lax429075.Encoding.parseLiteral
end Lax429075.Encoding.parseLiteral

namespace Lax429075.Encoding.parseNat
end Lax429075.Encoding.parseNat

namespace Lax429075.Encoding

open CNF Lax434930.PolynomialTime

def encodeList {α : Type} (encode : α → Word) : List α → Word
  | [] => [false]
  | a :: as => true :: (encode a ++ encodeList encode as)

def encodeNat (n : ℕ) : Word := List.replicate n true ++ [false]

def encodeLiteral (l : Literal) : Word := encodeNat l.index ++ [l.positive]

def encodeClause : Clause → Word := encodeList encodeLiteral

def encodeCNF : Formula → Word := encodeList encodeClause

end Lax429075.Encoding
end

-- Lax429075.Satisfiability
section
namespace Lax429075.Satisfiability
end Lax429075.Satisfiability
end

-- Lax888481.Scheduling
section
namespace Lax888481
end Lax888481

namespace Lax888481.Scheduling
end Lax888481.Scheduling

namespace Lax888481.Scheduling.Instance
end Lax888481.Scheduling.Instance
end

-- Lax888481.BinaryEncoding
section
namespace Lax888481.BinaryEncoding
end Lax888481.BinaryEncoding
end

-- Lax888481.NPHardness
section
namespace Lax888481.NPHardness
end Lax888481.NPHardness
end

-- Lax888481.SatVariant
section
namespace Lax888481.SatVariant

open Lax429075.CNF Lax434930.PolynomialTime

/-- The number of occurrences of the variable `i` in the formula `F`. -/
def occurrences (F : Formula) (i : ℕ) : ℕ :=
  (F.flatMap fun C => C.filter fun l => l.index == i).length

/-- The variables occurring in `F`. -/
def occurringVars (F : Formula) : List ℕ := (F.flatMap id).map Literal.index

/-- `F` is a *(3,4)* formula: every clause has exactly three literals, and every variable
occurs at most four times. -/
def Exact34 (F : Formula) : Prop :=
  (∀ C ∈ F, C.length = 3) ∧ ∀ i ∈ occurringVars F, occurrences F i ≤ 4

/-- **(3,4)-SAT** as a language: the encodings of satisfiable (3,4)
formulas. -/
def SAT34 : Language :=
  {w | ∃ F : Formula, Lax429075.Encoding.encodeCNF F = w ∧ Exact34 F ∧ Satisfiable F}

/-- **Tovey's theorem.** (3,4)-SAT is NP-hard.

Tovey, *A simplified NP-complete satisfiability problem*, Discrete Applied Mathematics 8
(1984) 85–89. -/
axiom sat34_npHard :
    ∀ A : Language, A ∈ Lax434930.NondeterministicPolynomialTime.NP →
      Lax429075.Reductions.ManyOne A SAT34

end Lax888481.SatVariant
end
