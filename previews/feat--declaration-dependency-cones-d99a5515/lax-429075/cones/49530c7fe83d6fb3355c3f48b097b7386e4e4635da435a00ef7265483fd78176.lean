-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Computability.TuringMachine.Computable

-- Lax434930.PolynomialTime
section
namespace Lax434930.PolynomialTime

/-- A finite binary string. -/
abbrev Word := List Bool

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

end Lax429075.CNF
end

-- Lax429075.Encoding
section
namespace Lax429075.Encoding.decodeCNF
end Lax429075.Encoding.decodeCNF

namespace Lax429075.Encoding.encodeList
end Lax429075.Encoding.encodeList

namespace Lax429075.Encoding

open CNF Lax434930.PolynomialTime

def parseNat : Word → Option (ℕ × Word)
  | [] => none
  | false :: w => some (0, w)
  | true :: w => do
    let (n, rest) ← parseNat w
    pure (n + 1, rest)

def parseLiteral (w : Word) : Option (Literal × Word) := do
  let (n, rest) ← parseNat w
  match rest with
  | [] => none
  | sign :: tail => pure (⟨n, sign⟩, tail)

def parseList {α : Type} (parse : Word → Option (α × Word)) :
    ℕ → Word → Option (List α × Word)
  | 0, _ => none
  | _ + 1, [] => none
  | _ + 1, false :: w => some ([], w)
  | fuel + 1, true :: w => do
    let (a, rest) ← parse w
    let (as, tail) ← parseList parse fuel rest
    pure (a :: as, tail)

def parseClause (w : Word) : Option (Clause × Word) := parseList parseLiteral w.length w

end Lax429075.Encoding
end
