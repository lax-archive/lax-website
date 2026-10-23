-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Computability.TuringMachine.Computable

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

-- Lax429075.Circuits
section
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

structure Circuit where
  gates : List Gate
  output : Fin gates.length
  ordered : ∀ g i, (g, i) ∈ gates.zipIdx → ∀ j ∈ g.inputs, j < i

def Gate.check (ρ : Assignment) (i : ℕ) : Gate → Bool
  | .input => true
  | .constant b => ρ i == b
  | .neg a => ρ i == !(ρ a)
  | .conj a b => ρ i == (ρ a && ρ b)
  | .disj a b => ρ i == (ρ a || ρ b)

def check (C : Circuit) (ρ : Assignment) : Bool :=
  ρ C.output && C.gates.zipIdx.all (fun gi => gi.1.check ρ gi.2)

def Satisfiable (C : Circuit) : Prop := ∃ ρ, check C ρ = true

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

def encode (C : Circuit) : Formula :=
  [[positive C.output]] ++ C.gates.zipIdx.flatMap (fun gi => gateClauses gi.2 gi.1)

end Lax429075.Tseitin
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
end Lax434930.NondeterministicPolynomialTime
end

-- Lax429075.CircuitMachine
section
namespace Lax429075.CircuitMachine

open Lax434930.PolynomialTime Lax434930.Certificates Circuits Encoding

axiom compile (V : Language) (hV : V ∈ P) (p : Polynomial ℕ) :
  ∃ circuits : Word → Circuit,
    Nonempty (Turing.TM2ComputableInPolyTime id id
      (fun x => encodeCNF (Tseitin.encode (circuits x)))) ∧
    ∀ x, Satisfiable (circuits x) ↔
      ∃ y : Word, y.length ≤ p.eval x.length ∧ pair x y ∈ V

end Lax429075.CircuitMachine
end
