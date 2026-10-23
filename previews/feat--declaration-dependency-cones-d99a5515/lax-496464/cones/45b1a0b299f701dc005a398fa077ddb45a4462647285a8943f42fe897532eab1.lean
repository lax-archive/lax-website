-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Finset.Card

-- Lax496464.WH_B1_Structures
section
namespace Lax496464.WH_B1_Structures

open scoped BigOperators

/-- A finite relational structure. -/
structure Structure where
  /-- The vocabulary: the arities of the relation symbols `0, 1, …`. -/
  arities : List ℕ
  /-- The universe is `{0, …, size - 1}`. -/
  size : ℕ
  /-- The relation of each symbol, as a set of tuples. -/
  rel : ℕ → Finset (List ℕ)
  /-- Every arity is at least one. -/
  arity_pos : ∀ a ∈ arities, 1 ≤ a
  /-- The tuples of symbol `i` have its arity and entries in the universe; other symbols have no
  tuples. -/
  wf : ∀ i, ∀ t ∈ rel i, i < arities.length ∧ t.length = arities.getD i 0 ∧ ∀ a ∈ t, a < size

/-- The block of one relation: the number of its tuples, then the tuples, in some order without
repetition. -/
def EncodesRel (R : Finset (List ℕ)) (blk : List ℕ) : Prop :=
  ∃ ts : List (List ℕ), ts.Nodup ∧ ts.toFinset = R ∧ blk = ts.length :: ts.flatten

/-- The word `x` is an encoding of the structure `A`: the number of symbols, the arities, the size
of the universe, and one block per symbol. -/
def Encodes (x : List ℕ) (A : Structure) : Prop :=
  ∃ blocks : List (List ℕ), blocks.length = A.arities.length ∧
    (∀ i < A.arities.length, EncodesRel (A.rel i) (blocks.getD i [])) ∧
    x = A.arities.length :: (A.arities ++ A.size :: blocks.flatten)

end Lax496464.WH_B1_Structures
end
