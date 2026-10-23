-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.VertexCover
import Mathlib.Computability.Partrec
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Set.Basic
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

/-- The bit-size of a finite list of natural numbers. -/
def bitSize (x : List ℕ) : ℕ :=
  (encode x).length

end Lax759944.BinaryWordEncoding
end

-- Lax808846.Ram
section
namespace Lax808846.Ram

/-- An instruction. Every number naming a cell is read, except that
the first one names the destination for instructions that write a cell,
and the cell holding the destination address for `store`. `set` carries
a literal value; `jump`, `jzero`, and `jeof` carry program labels,
which are not data-memory addresses. -/
inductive Instr
  /-- Set cell `a` to the literal `n`. -/
  | set (a n : ℕ)
  /-- Set cell `a` to the contents of the cell whose address cell `b`
  holds. -/
  | load (a b : ℕ)
  /-- Set the cell whose address cell `a` holds to the contents of cell
  `b`. -/
  | store (a b : ℕ)
  /-- Set cell `a` to the sum of cells `b` and `c`, wrapping around
  modulo `2 ^ w`. -/
  | add (a b c : ℕ)
  /-- Set cell `a` to the difference of cells `b` and `c`, truncated at
  zero rather than wrapping around. -/
  | sub (a b c : ℕ)
  /-- Set cell `a` to the product of cells `b` and `c`, wrapping around
  modulo `2 ^ w`. -/
  | mul (a b c : ℕ)
  /-- Set cell `a` to the quotient of cells `b` and `c`, rounding
  towards zero; division by zero yields zero. -/
  | div (a b c : ℕ)
  /-- Set cell `a` to the bitwise conjunction of cells `b` and `c`. -/
  | and (a b c : ℕ)
  /-- Set cell `a` to cell `b` shifted left by the number of bits cell
  `c` holds, wrapping around modulo `2 ^ w`; a shift by `w` or more
  yields zero. -/
  | shiftl (a b c : ℕ)
  /-- Set cell `a` to the bitwise complement `2 ^ w - 1 - m[b]` of cell
  `b` within the word length. -/
  | not (a b : ℕ)
  /-- Continue at instruction `l`. -/
  | jump (l : ℕ)
  /-- Continue at instruction `l` if cell `a` is zero. -/
  | jzero (a l : ℕ)
  /-- Continue at instruction `l` exactly when the remaining input tape
  is empty. This test does not consume input. -/
  | jeof (l : ℕ)
  /-- Write the original input length, reduced to a word, into cell `a`. -/
  | inputLength (a : ℕ)
  /-- Read original input at the word index in cell `b` into cell `a`,
  returning zero outside the input. Read the index before writing `a`,
  even when the two cell addresses coincide. Do not consume input. -/
  | inputLoad (a b : ℕ)
  /-- Halt. -/
  | halt
  /-- Read the next number of the input tape into cell `a`, or halt if
  the tape is exhausted. -/
  | read (a : ℕ)
  /-- Append the contents of cell `a` to the output tape. -/
  | write (a : ℕ)

/-- A program: a finite sequence of instructions, numbered from `0`. -/
abbrev Program : Type := List Instr

/-- A machine state: the program counter, the contents of every memory
cell, the immutable original input array, the remaining sequential input
tape, and the output tape written so far. -/
structure State where
  /-- The number of the instruction to be executed next. -/
  pc : ℕ
  /-- The contents of the memory cells; only the cells with number below
  `2 ^ w` are ever addressed. -/
  mem : ℕ → ℕ
  /-- The original read-only input, unchanged by every instruction. -/
  input : List ℕ
  /-- The numbers still to be read from the input tape. -/
  inp : List ℕ
  /-- The numbers written to the output tape so far. -/
  out : List ℕ

/-- The memory `m` with cell `a` set to `v`, at word length `w`: the
address and the value written are both taken modulo `2 ^ w`. -/
def setCell (w : ℕ) (m : ℕ → ℕ) (a v : ℕ) : ℕ → ℕ :=
  fun b => if b = a % 2 ^ w then v % 2 ^ w else m b

/-- The effect of one instruction on the state at word length `w`, or
`none` if it halts the machine, which a `halt` instruction and a read
from an exhausted input tape do. Data values, input indices, and
data-memory addresses are reduced modulo `2 ^ w`; program labels and
the counter are not. -/
def Instr.effect (w : ℕ) : Instr → State → Option State
  | set a n, s => some { s with pc := s.pc + 1, mem := setCell w s.mem a n }
  | load a b, s =>
      some
        { s with
          pc := s.pc + 1
          mem := setCell w s.mem a (s.mem (s.mem (b % 2 ^ w) % 2 ^ w)) }
  | store a b, s =>
      some
        { s with
          pc := s.pc + 1
          mem := setCell w s.mem (s.mem (a % 2 ^ w)) (s.mem (b % 2 ^ w)) }
  | add a b c, s =>
      some
        { s with
          pc := s.pc + 1
          mem := setCell w s.mem a (s.mem (b % 2 ^ w) + s.mem (c % 2 ^ w)) }
  | sub a b c, s =>
      some
        { s with
          pc := s.pc + 1
          mem := setCell w s.mem a (s.mem (b % 2 ^ w) - s.mem (c % 2 ^ w)) }
  | mul a b c, s =>
      some
        { s with
          pc := s.pc + 1
          mem := setCell w s.mem a (s.mem (b % 2 ^ w) * s.mem (c % 2 ^ w)) }
  | div a b c, s =>
      some
        { s with
          pc := s.pc + 1
          mem := setCell w s.mem a (s.mem (b % 2 ^ w) / s.mem (c % 2 ^ w)) }
  | and a b c, s =>
      some
        { s with
          pc := s.pc + 1
          mem := setCell w s.mem a (Nat.land (s.mem (b % 2 ^ w)) (s.mem (c % 2 ^ w))) }
  | shiftl a b c, s =>
      some
        { s with
          pc := s.pc + 1
          mem := setCell w s.mem a (s.mem (b % 2 ^ w) * 2 ^ s.mem (c % 2 ^ w)) }
  | not a b, s =>
      some
        { s with
          pc := s.pc + 1
          mem := setCell w s.mem a (2 ^ w - 1 - s.mem (b % 2 ^ w)) }
  | jump l, s => some { s with pc := l }
  | jzero a l, s => some { s with pc := if s.mem (a % 2 ^ w) = 0 then l else s.pc + 1 }
  | jeof l, s => some { s with pc := if s.inp.isEmpty then l else s.pc + 1 }
  | inputLength a, s =>
      some { s with pc := s.pc + 1, mem := setCell w s.mem a s.input.length }
  | inputLoad a b, s =>
      some { s with
        pc := s.pc + 1
        mem := setCell w s.mem a (s.input[s.mem (b % 2 ^ w) % 2 ^ w]?.getD 0) }
  | halt, _ => none
  | read a, s =>
      s.inp.head?.map fun v =>
        { s with pc := s.pc + 1, mem := setCell w s.mem a v, inp := s.inp.tail }
  | write a, s =>
      some { s with pc := s.pc + 1, out := s.out ++ [s.mem (a % 2 ^ w) % 2 ^ w] }

/-- One step of the machine at word length `w`: fetch the instruction
the program counter points at and execute it. The result is `none` if
the machine has halted, which also happens when the program counter has
run past the program. -/
def step (w : ℕ) (p : Program) (s : State) : Option State :=
  p[s.pc]?.bind fun i => i.effect w s

/-- The state after `t` successful transitions at word length `w`, or
`none` if one of those transitions terminates. This auxiliary count does
not include a fetched terminal instruction; `RunsTo` charges that too. -/
def run (w : ℕ) (p : Program) : ℕ → State → Option State
  | 0, s => some s
  | t + 1, s => (step w p s).bind (run w p t)

/-- The initial state on input `x`: program counter zero, all memory
cells zero, the original input array and its sequential tape both `x`,
and the output tape empty. -/
def initState (x : List ℕ) : State where
  pc := 0
  mem := fun _ => 0
  input := x
  inp := x
  out := []

/-- Cost of termination at `s`, when `step w p s = none`: a fetched
terminal instruction costs one, while an out-of-range program counter
costs zero because there is no instruction to execute. -/
def terminalCost (p : Program) (s : State) : ℕ :=
  if s.pc < p.length then 1 else 0

/-- Started on input `x` at word length `w`, the machine executes
exactly `t` instructions and then halts, having written the word `y` to
its output tape. -/
def RunsTo (w : ℕ) (p : Program) (x y : List ℕ) (t : ℕ) : Prop :=
  ∃ (k : ℕ) (s : State), run w p k (initState x) = some s ∧
    step w p s = none ∧ s.out = y ∧ t = k + terminalCost p s

end Lax808846.Ram
end

-- Lax759944.RamPolytime
section
namespace Lax759944.RamPolytime

open Lax808846.Ram

open Lax759944.BinaryWordEncoding

/-- Every entry of `x` is representable by a word of `w` bits. -/
def FitsInWords (w : ℕ) (x : List ℕ) : Prop :=
  ∀ a ∈ x, a < 2 ^ w

end Lax759944.RamPolytime
end

-- Lax496464.WH_A1_FptTime
section
namespace Lax496464.WH_A1_FptTime

open Lax808846.Ram Lax759944.BinaryWordEncoding Lax759944.RamPolytime

/-- The fixed-parameter bound `f(k) · (n + 1)^d`, for a parameter value `k` and an input size `n`. -/
def fptBound (f : ℕ → ℕ) (d k n : ℕ) : ℕ := f k * (n + 1) ^ d

/-- On every word `x` of `D`, the program `p` computes `F x` from the tape `x.length :: x`
within `B = f(κ x) · (bitSize x + 1)^d` instructions, at every word length `w ≥ B`; and the
tape and the output fit in words of length `B`. -/
def ComputesInFptTime (p : Program) (D : Set (List ℕ)) (κ : List ℕ → ℕ)
    (F : List ℕ → List ℕ) (f : ℕ → ℕ) (d : ℕ) : Prop :=
  ∀ x ∈ D,
    FitsInWords (fptBound f d (κ x) (bitSize x)) ((x.length :: x) ++ F x) ∧
      ∀ w : ℕ, fptBound f d (κ x) (bitSize x) ≤ w →
        ∃ t ≤ fptBound f d (κ x) (bitSize x), RunsTo w p (x.length :: x) (F x) t

/-- **Fixed-parameter time.** `F` is computable on the words of `D` in time `f(κ x) · (|x| + 1)^d`
by one program, for a computable `f` and a constant `d`. -/
def FptTimeOn (D : Set (List ℕ)) (κ : List ℕ → ℕ) (F : List ℕ → List ℕ) : Prop :=
  ∃ (p : Program) (f : ℕ → ℕ) (d : ℕ), Computable f ∧ ComputesInFptTime p D κ F f d

/-- **Polynomial time.** `F` is computable on the words of `D` in time `c · (|x| + 1)^d` by one
program. -/
def PolyTimeOn (D : Set (List ℕ)) (F : List ℕ → List ℕ) : Prop :=
  ∃ (p : Program) (c d : ℕ), ComputesInFptTime p D (fun _ => 0) F (fun _ => c) d

end Lax496464.WH_A1_FptTime
end

-- Lax808846.RamComputes
section
namespace Lax808846.RamComputes

open Lax808846.Ram

/-- At word length `w`, on every admissible input `x`, the program halts
within `T x` executed instructions with output `f x`. -/
def ComputesInTime (w : ℕ) (p : Program) (D : Set (List ℕ))
    (f : List ℕ → List ℕ) (T : List ℕ → ℕ) : Prop :=
  ∀ x ∈ D, ∃ t ≤ T x, RunsTo w p x (f x) t

end Lax808846.RamComputes
end

-- Lax888481.ParameterizedComplexity
section
namespace Lax888481.ParameterizedComplexity

open Lax808846.Ram Lax808846.RamComputes

/-- A parameterized problem: the words that encode an instance, which of them are
yes-instances, and the parameter each one carries. -/
structure Problem where
  /-- The words that encode an instance. A program may do anything on the others. -/
  Domain : Set (List ℕ)
  /-- The yes-instances. -/
  Yes : List ℕ → Prop
  /-- The parameter, read off the word. -/
  param : List ℕ → ℕ

/-- The word `x` fits at word length `w`, with room for `c` times its length: every
entry `v` of `x` satisfies `c * (x.length + v + 1) ≤ 2 ^ w`. -/
def Fits (c w : ℕ) (x : List ℕ) : Prop := ∀ v ∈ x, c * (x.length + v + 1) ≤ 2 ^ w

/-- The map `f` is an fpt-reduction from `P` to `Q`, computed by `prog` within
`c * g k * (|x| + 1)` instructions and raising the parameter by at most `h`. -/
structure IsFptReduction (P Q : Problem) (f : List ℕ → List ℕ) (prog : Program)
    (c : ℕ) (g h : ℕ → ℕ) : Prop where
  /-- The image of an admissible word is admissible. -/
  maps_domain : ∀ x ∈ P.Domain, f x ∈ Q.Domain
  /-- Yes-instances go to yes-instances, and no-instances to no-instances. -/
  correct : ∀ x ∈ P.Domain, (P.Yes x ↔ Q.Yes (f x))
  /-- The new parameter is bounded by a function of the old one alone. -/
  param_le : ∀ x ∈ P.Domain, Q.param (f x) ≤ h (P.param x)
  /-- At every word length, the program computes `f` on every admissible word that fits
  and whose image fits, within the stated bound. -/
  time : ∀ w : ℕ, ComputesInTime w prog
    {x | x ∈ P.Domain ∧ Fits c w x ∧ Fits c w (f x)}
    f (fun x => c * g (P.param x) * (x.length + 1))

/-- `P` **fpt-reduces** to `Q`. -/
def FptReduces (P Q : Problem) : Prop :=
  ∃ (f : List ℕ → List ℕ) (prog : Program) (c : ℕ) (g h : ℕ → ℕ),
    IsFptReduction P Q f prog c g h

@[inherit_doc] infix:50 " ≤fpt " => FptReduces

end Lax888481.ParameterizedComplexity
end

-- Lax496464.WH_A2_FptReductions
section
namespace Lax496464.WH_A2_FptReductions

open Lax888481.ParameterizedComplexity (Problem)

open Lax496464.WH_A1_FptTime

/-- **Step 1 of a reduction: construction and correctness.** `R` maps instances of `P` to
instances of `Q`, yes-instances to yes-instances and no-instances to no-instances. -/
structure IsReduction (P Q : Problem) (R : List ℕ → List ℕ) : Prop where
  /-- Instances go to instances. -/
  maps_domain : ∀ x ∈ P.Domain, R x ∈ Q.Domain
  /-- Yes-instances go to yes-instances, and no-instances to no-instances. -/
  correct : ∀ x ∈ P.Domain, (P.Yes x ↔ Q.Yes (R x))

/-- **Step 2 of a reduction: the parameter bound.** The parameter of `R x` is at most a computable
function of the parameter of `x`. -/
def ParamBounded (P Q : Problem) (R : List ℕ → List ℕ) : Prop :=
  ∃ g : ℕ → ℕ, Computable g ∧ ∀ x ∈ P.Domain, Q.param (R x) ≤ g (P.param x)

/-- An **fpt-reduction** [FG06, Definition 2.1]: a reduction with a bounded parameter,
computable in fixed-parameter time (**step 3**) on the instances of `P`. -/
structure IsFptReduction (P Q : Problem) (R : List ℕ → List ℕ) : Prop where
  /-- Construction and correctness. -/
  reduction : IsReduction P Q R
  /-- The parameter bound. -/
  param_bounded : ParamBounded P Q R
  /-- The running time. -/
  fpt_time : FptTimeOn P.Domain P.param R

/-- `P` **fpt-reduces** to `Q`. -/
def FptReduces (P Q : Problem) : Prop := ∃ R, IsFptReduction P Q R

@[inherit_doc] scoped infix:50 " ≤ᶠᵖᵗ " => FptReduces

/-- `P` is a **parameterized problem**: its parameter is computable
in polynomial time on its instances [FG06, Definition 1.1]. -/
def IsParameterized (P : Problem) : Prop := PolyTimeOn P.Domain fun x => [P.param x]

/-- `[C]^fpt`: the parameterized problems that fpt-reduce to a member of `C`. -/
def Closure (C : Set Problem) : Set Problem :=
  {P | IsParameterized P ∧ ∃ Q ∈ C, P ≤ᶠᵖᵗ Q}

/-- `Q` is **`C`-hard**: every member of `C` fpt-reduces to it. -/
def Hard (C : Set Problem) (Q : Problem) : Prop := ∀ P ∈ C, P ≤ᶠᵖᵗ Q

/-- `Q` is **`C`-complete**: it belongs to `C` and is `C`-hard. -/
def Complete (C : Set Problem) (Q : Problem) : Prop := Q ∈ C ∧ Hard C Q

end Lax496464.WH_A2_FptReductions
end

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

-- Lax496464.WH_B2_FirstOrder
section
namespace Lax496464.WH_B2_FirstOrder.Formula.ArityAtMost
end Lax496464.WH_B2_FirstOrder.Formula.ArityAtMost

namespace Lax496464.WH_B2_FirstOrder.Formula.IsPositive
end Lax496464.WH_B2_FirstOrder.Formula.IsPositive

namespace Lax496464.WH_B2_FirstOrder.Formula.NoSetVar
end Lax496464.WH_B2_FirstOrder.Formula.NoSetVar

namespace Lax496464.WH_B2_FirstOrder

open Lax496464.WH_B1_Structures

/-- First-order formulas, with atoms for the vocabulary's relation symbols and for one free relation
variable. -/
inductive Formula
  /-- The atom `R_i x_{a_1} … x_{a_r}`. -/
  | rel (i : ℕ) (xs : List ℕ)
  /-- The atom `X x_{a_1} … x_{a_s}` of the free relation variable. -/
  | setVar (xs : List ℕ)
  /-- The equation `x = y`. -/
  | eq (x y : ℕ)
  /-- Negation. -/
  | neg (φ : Formula)
  /-- Conjunction. -/
  | and (φ ψ : Formula)
  /-- Disjunction. -/
  | or (φ ψ : Formula)
  /-- Existential quantification. -/
  | ex (x : ℕ) (φ : Formula)
  /-- Universal quantification. -/
  | all (x : ℕ) (φ : Formula)

/-- An assignment of universe elements to variables. -/
abbrev Assignment := ℕ → ℕ

/-- The assignment `ρ` changed to send `x` to `a`. -/
def Assignment.update (ρ : Assignment) (x a : ℕ) : Assignment :=
  fun y => if y = x then a else ρ y

/-- **Satisfaction.** The formula holds in `A`, with the relation variable interpreted as `S`,
under the assignment `ρ`. -/
def Sat (A : Structure) (S : Set (List ℕ)) : Formula → Assignment → Prop
  | .rel i xs, ρ => xs.map ρ ∈ A.rel i
  | .setVar xs, ρ => xs.map ρ ∈ S
  | .eq x y, ρ => ρ x = ρ y
  | .neg φ, ρ => ¬ Sat A S φ ρ
  | .and φ ψ, ρ => Sat A S φ ρ ∧ Sat A S ψ ρ
  | .or φ ψ, ρ => Sat A S φ ρ ∨ Sat A S ψ ρ
  | .ex x φ, ρ => ∃ a, a < A.size ∧ Sat A S φ (ρ.update x a)
  | .all x φ, ρ => ∀ a, a < A.size → Sat A S φ (ρ.update x a)

/-- The free (individual) variables of a formula. -/
def Formula.freeVars : Formula → Finset ℕ
  | .rel _ xs => xs.toFinset
  | .setVar xs => xs.toFinset
  | .eq x y => {x, y}
  | .neg φ => φ.freeVars
  | .and φ ψ => φ.freeVars ∪ ψ.freeVars
  | .or φ ψ => φ.freeVars ∪ ψ.freeVars
  | .ex x φ => φ.freeVars.erase x
  | .all x φ => φ.freeVars.erase x

/-- The formula is a **sentence**: it has no free individual variables (the relation variable may
occur). -/
def IsSentence (φ : Formula) : Prop := φ.freeVars = ∅

/-- The formula fits the vocabulary `arities`, and uses the relation variable at arity `s`. -/
def Formula.Fits (arities : List ℕ) (s : ℕ) : Formula → Prop
  | .rel i xs => i < arities.length ∧ xs.length = arities.getD i 0
  | .setVar xs => xs.length = s
  | .eq _ _ => True
  | .neg φ => φ.Fits arities s
  | .and φ ψ => φ.Fits arities s ∧ ψ.Fits arities s
  | .or φ ψ => φ.Fits arities s ∧ ψ.Fits arities s
  | .ex _ φ => φ.Fits arities s
  | .all _ φ => φ.Fits arities s

/-- The formula is quantifier-free. -/
def Formula.IsQF : Formula → Prop
  | .ex _ _ => False
  | .all _ _ => False
  | .neg φ => φ.IsQF
  | .and φ ψ => φ.IsQF ∧ ψ.IsQF
  | .or φ ψ => φ.IsQF ∧ ψ.IsQF
  | _ => True

/-- A block of existential quantifiers over the variables `xs`. -/
def Formula.exBlock (xs : List ℕ) (φ : Formula) : Formula := xs.foldr Formula.ex φ

/-- A block of universal quantifiers over the variables `xs`. -/
def Formula.allBlock (xs : List ℕ) (φ : Formula) : Formula := xs.foldr Formula.all φ

/-- `Alt true t φ` is `φ ∈ Σ_t` and `Alt false t φ` is `φ ∈ Π_t`: `t` alternating blocks of
quantifiers, the first existential or universal respectively, in front of a quantifier-free
formula. -/
def Alt : Bool → ℕ → Formula → Prop
  | _, 0, φ => φ.IsQF
  | true, t + 1, φ => ∃ xs ψ, φ = Formula.exBlock xs ψ ∧ Alt false t ψ
  | false, t + 1, φ => ∃ xs ψ, φ = Formula.allBlock xs ψ ∧ Alt true t ψ

/-- `φ ∈ Π_t`. -/
abbrev IsPi (t : ℕ) (φ : Formula) : Prop := Alt false t φ

end Lax496464.WH_B2_FirstOrder
end

-- Lax496464.WH_B3_LogicProblems
section
namespace Lax496464.WH_B3_LogicProblems

open Lax496464.WH_B1_Structures Lax496464.WH_B2_FirstOrder

open Lax888481.ParameterizedComplexity (Problem)

/-- The word `x` is the word of the structure `A` followed by the number `k`. -/
def EncodesWD (x : List ℕ) (A : Structure) (k : ℕ) : Prop :=
  ∃ y, Encodes y A ∧ x = y ++ [k]

/-- A **witness** of weight `k` for `φ(X)` in `A`, with `X` of arity `s`: a set of `k` tuples of
length `s` over the universe that, taken as the value of `X`, makes `φ` true. -/
def Witness (A : Structure) (φ : Formula) (s k : ℕ) : Prop :=
  φ.Fits A.arities s ∧ ∃ S : Finset (List ℕ), S.card = k ∧
    (∀ t ∈ S, t.length = s ∧ ∀ a ∈ t, a < A.size) ∧ Sat A ↑S φ fun _ => 0

/-- **`p-WD_φ`**, weighted Fagin definability of `φ(X)` with `X` of arity `s`. -/
def pWD (φ : Formula) (s : ℕ) : Problem where
  Domain := {x | ∃ A k, EncodesWD x A k}
  Yes x := ∃ A k, EncodesWD x A k ∧ Witness A φ s k
  param x := x.getLast?.getD 0

end Lax496464.WH_B3_LogicProblems
end

-- Lax496464.WH_B4_Hierarchies
section
namespace Lax496464.WH_B4_Hierarchies

open Lax496464.WH_B2_FirstOrder Lax496464.WH_B3_LogicProblems Lax496464.WH_A2_FptReductions

open Lax888481.ParameterizedComplexity (Problem)

/-- **`p-WD-Π_t`**: the weighted definability problems of `Π_t`-sentences. -/
def pWDPi (t : ℕ) : Set Problem :=
  {P | ∃ (φ : Formula) (s : ℕ), IsPi t φ ∧ IsSentence φ ∧ P = pWD φ s}

/-- **`W[t]`**, the `t`-th class of the W-hierarchy. -/
def W (t : ℕ) : Set Problem := Closure (pWDPi t)

end Lax496464.WH_B4_Hierarchies
end

-- Lax271696.GraphEncoding
section
namespace Lax271696.GraphEncoding

/-- The number of vertices declared by a word: its first entry. -/
def vertexCount (x : List ℕ) : ℕ := x.getD 0 0

/-- The number of edges declared by a word: its second entry. -/
def edgeCount (x : List ℕ) : ℕ := x.getD 1 0

/-- The `i`-th offset of a word: the `n+1` offsets follow the two
header entries. -/
def offset (x : List ℕ) (i : ℕ) : ℕ := x.getD (2 + i) 0

/-- The `j`-th entry of the target array of a word, which follows the
header and the offsets. -/
def target (x : List ℕ) (j : ℕ) : ℕ := x.getD (3 + vertexCount x + j) 0

/-- The word `x` is a compressed sparse row encoding of the graph `G`
on `n` vertices. -/
structure EncodesGraph (x : List ℕ) (n : ℕ) (G : SimpleGraph (Fin n)) :
    Prop where
  /-- The word declares `n` vertices. -/
  vertexCount_eq : vertexCount x = n
  /-- The word consists of the two header entries, the `n+1` offsets,
  and a target array of length twice the declared number of edges. -/
  length_eq : x.length = 3 + n + 2 * edgeCount x
  /-- The block of the first vertex begins at the start of the target
  array. -/
  offset_zero : offset x 0 = 0
  /-- The block of the last vertex ends at the end of the target
  array. -/
  offset_last : offset x n = 2 * edgeCount x
  /-- The offsets are nondecreasing, so they cut the target array into
  one block per vertex. -/
  offset_mono : ∀ i < n, offset x i ≤ offset x (i + 1)
  /-- Every entry of the target array is a vertex. -/
  target_lt : ∀ j < 2 * edgeCount x, target x j < n
  /-- The block of a vertex lists exactly its neighbors. -/
  adj_iff : ∀ u v : Fin n, G.Adj u v ↔
    ∃ j, offset x u ≤ j ∧ j < offset x (u + 1) ∧ target x j = v

end Lax271696.GraphEncoding
end

-- Lax271696.VertexCover
section
namespace Lax271696.VertexCover
end Lax271696.VertexCover
end

-- Lax496464.WH_C1_GraphProblems
section
namespace Lax496464
end Lax496464

namespace Lax496464.WH_C1_GraphProblems
end Lax496464.WH_C1_GraphProblems
end

-- Lax888481.MulticolouredClique
section
namespace Lax888481.MulticolouredClique

/-- An instance of Multicoloured Clique: a graph whose vertices are coloured so that
adjacent vertices differ in colour. -/
structure Instance where
  /-- The number `k` of colours, the parameter. -/
  colours : ℕ
  /-- The number `n` of vertices. -/
  vertices : ℕ
  /-- The graph. -/
  graph : SimpleGraph (Fin vertices)
  /-- The colour of each vertex. -/
  colour : Fin vertices → Fin colours
  /-- Adjacent vertices differ in colour. -/
  adj_colour_ne : ∀ u v, graph.Adj u v → colour u ≠ colour v

/-- `G` contains a multicoloured clique: one vertex of each colour, pairwise adjacent. -/
def Instance.HasMulticolouredClique (G : Instance) : Prop :=
  ∃ f : Fin G.colours → Fin G.vertices,
    (∀ c, G.colour (f c) = c) ∧ ∀ c c', c ≠ c' → G.graph.Adj (f c) (f c')

/-- The word `x` presents the instance `G`: a compressed sparse row block encoding the
graph, with each adjacency list strictly increasing, followed by one entry per vertex
giving its colour, followed by the number of colours. -/
def EncodesInstance (x : List ℕ) (G : Instance) : Prop :=
  ∃ g, x = g ++ (List.ofFn fun v => (G.colour v : ℕ)) ++ [G.colours] ∧
    Lax271696.GraphEncoding.EncodesGraph g G.vertices G.graph ∧
    ∀ u < G.vertices, ∀ t, Lax271696.GraphEncoding.offset g u ≤ t →
      t + 1 < Lax271696.GraphEncoding.offset g (u + 1) →
      Lax271696.GraphEncoding.target g t < Lax271696.GraphEncoding.target g (t + 1)

/-- The words that encode an instance. -/
def Instances : Set (List ℕ) := {x | ∃ G, EncodesInstance x G}

/-- **Multicoloured Clique**, parameterized by the number of colours. The parameter is
the last entry of the word. -/
def problem : ParameterizedComplexity.Problem where
  Domain := Instances
  Yes x := ∃ G, EncodesInstance x G ∧ G.HasMulticolouredClique
  param x := x.getLast? |>.getD 0

end Lax888481.MulticolouredClique
end

-- Lax496464.WH_D12_MulticolouredClique
section
namespace Lax496464.WH_D12_MulticolouredClique

open Lax496464.WH_B4_Hierarchies Lax496464.WH_A2_FptReductions Lax496464.WH_C1_GraphProblems

/-- **Multicoloured Clique is W[1]-complete.** -/
axiom multicolouredClique_W1_complete : Complete (W 1) Lax888481.MulticolouredClique.problem

end Lax496464.WH_D12_MulticolouredClique
end
