-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.DeriveFintype

-- Lax350013.StructuredPrograms
section
namespace Lax350013.StructuredPrograms

open Finset

/-- The operations on two words. -/
inductive Op : Type
  | add | sub | mul
  deriving DecidableEq, Repr

/-- The result of an operation. -/
def Op.eval : Op → ℤ → ℤ → ℤ
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .mul, a, b => a * b

/-- Expressions: constants, local variables, operations, and the content of the memory cell at an
address. -/
inductive Expr : Type
  | const (n : ℕ)
  | var (x : ℕ)
  | op (o : Op) (a b : Expr)
  | load (a : Expr)
  deriving Repr

/-- Tests. -/
inductive Cond : Type
  | lt (a b : Expr)
  | eq (a b : Expr)
  deriving Repr

/-- Statements.  `call p args x` runs procedure number p on the values of args and puts its result
into x. -/
inductive Stmt : Type
  | skip
  | set (x : ℕ) (e : Expr)
  | store (a e : Expr)
  | seq (s₁ s₂ : Stmt)
  | ite (c : Cond) (s₁ s₂ : Stmt)
  | while (c : Cond) (s : Stmt)
  | call (p : ℕ) (args : List Expr) (x : ℕ)
  deriving Repr

/-- A program: the bodies of its procedures, numbered from 0. -/
abbrev Program : Type := List Stmt

/-- What a running procedure sees: its local variables and the memory. -/
structure State : Type where
  loc : ℕ → ℤ
  mem : ℕ → ℤ

/-- The limits on a run: largest absolute value of a word, number of memory cells, nesting depth of
calls. -/
structure Limits : Type where
  word : ℤ
  space : ℕ
  depth : ℕ

/-- The value of an expression. -/
def Expr.val (s : State) : Expr → ℤ
  | .const n => n
  | .var x => s.loc x
  | .op o a b => o.eval (a.val s) (b.val s)
  | .load a => s.mem (a.val s).toNat

/-- The number of steps that evaluating an expression takes: one for each of its constants,
variables, operations, loads. -/
def Expr.cost : Expr → ℕ
  | .const _ => 1
  | .var _ => 1
  | .op _ a b => a.cost + b.cost + 1
  | .load a => a.cost + 1

/-- An address within the limits. -/
def Limits.Addr (lim : Limits) (a : ℤ) : Prop := 0 ≤ a ∧ a < lim.space

/-- The evaluation of an expression stays within the limits: every value that is formed fits in a
word, and every address that is read is within the memory. -/
def Expr.Safe (lim : Limits) (s : State) : Expr → Prop
  | .const n => (n : ℤ) ≤ lim.word
  | .var _ => True
  | .op o a b => a.Safe lim s ∧ b.Safe lim s ∧ |o.eval (a.val s) (b.val s)| ≤ lim.word
  | .load a => a.Safe lim s ∧ lim.Addr (a.val s)

/-- Whether a test holds. -/
def Cond.Holds (s : State) : Cond → Prop
  | .lt a b => a.val s < b.val s
  | .eq a b => a.val s = b.val s

/-- The number of steps of a test: its two sides and the comparison. -/
def Cond.cost : Cond → ℕ
  | .lt a b => a.cost + b.cost + 1
  | .eq a b => a.cost + b.cost + 1

/-- The evaluation of a test stays within the limits. -/
def Cond.Safe (lim : Limits) (s : State) : Cond → Prop
  | .lt a b => a.Safe lim s ∧ b.Safe lim s
  | .eq a b => a.Safe lim s ∧ b.Safe lim s

/-- The local variables of a procedure that has just been called: the arguments in 0, 1, …, and 0 in
all others. -/
def frame (args : List ℤ) : ℕ → ℤ := fun i => args.getD i 0

/-- `Exec lim P d s σ σ' c`: within the limits lim, and at nesting depth d of calls, the statement
s of the program P, started in the state σ, ends in the state σ' after exactly c steps. -/
inductive Exec (lim : Limits) (P : Program) : ℕ → Stmt → State → State → ℕ → Prop
  | skip {d σ} : Exec lim P d .skip σ σ 0
  | set {d σ x e} : e.Safe lim σ →
      Exec lim P d (.set x e) σ { σ with loc := Function.update σ.loc x (e.val σ) } (e.cost + 1)
  | store {d σ a e} : a.Safe lim σ → e.Safe lim σ → lim.Addr (a.val σ) →
      Exec lim P d (.store a e) σ { σ with mem := Function.update σ.mem (a.val σ).toNat (e.val σ) }
        (a.cost + e.cost + 1)
  | seq {d σ σ' σ'' s₁ s₂ c₁ c₂} : Exec lim P d s₁ σ σ' c₁ → Exec lim P d s₂ σ' σ'' c₂ →
      Exec lim P d (.seq s₁ s₂) σ σ'' (c₁ + c₂)
  | iteTrue {d σ σ' c s₁ s₂ k} : c.Safe lim σ → c.Holds σ → Exec lim P d s₁ σ σ' k →
      Exec lim P d (.ite c s₁ s₂) σ σ' (c.cost + 1 + k)
  | iteFalse {d σ σ' c s₁ s₂ k} : c.Safe lim σ → ¬ c.Holds σ → Exec lim P d s₂ σ σ' k →
      Exec lim P d (.ite c s₁ s₂) σ σ' (c.cost + 1 + k)
  | whileFalse {d σ c s} : c.Safe lim σ → ¬ c.Holds σ → Exec lim P d (.while c s) σ σ (c.cost + 1)
  | whileTrue {d σ σ' σ'' c s k₁ k₂} : c.Safe lim σ → c.Holds σ → Exec lim P d s σ σ' k₁ →
      Exec lim P d (.while c s) σ' σ'' k₂ → Exec lim P d (.while c s) σ σ'' (c.cost + 1 + k₁ + k₂)
  | call {d σ σ' p args x body k} : (∀ e ∈ args, e.Safe lim σ) → P[p]? = some body → d < lim.depth →
      Exec lim P (d + 1) body ⟨frame (args.map (·.val σ)), σ.mem⟩ σ' k →
      Exec lim P d (.call p args x) σ ⟨Function.update σ.loc x (σ'.loc 0), σ'.mem⟩
        ((args.map Expr.cost).sum + 2 + k)

end Lax350013.StructuredPrograms
end

-- Lax350013.ProcedureContracts
section
namespace Lax350013.ProcedureContracts

open Finset

open Lax350013.StructuredPrograms

/-- The statement s, started in σ, ends within T steps in a state that satisfies Q. -/
def Ends (lim : Limits) (P : Program) (d : ℕ) (s : Stmt) (σ : State) (T : ℕ) (Q : State → Prop) :
    Prop :=
  ∃ σ' c, Exec lim P d s σ σ' c ∧ c ≤ T ∧ Q σ'

/-- The bound 2^s · ((p₁ + 1) (p₂ + 1) ⋯)^k in the parameters of an instance. -/
def polyBound (s k : ℕ) (params : List ℕ) : ℕ := 2 ^ s * ((params.map (· + 1)).prod) ^ k

/-- The cell `b` is not among the `n` cells from address `a`. -/
abbrev Outside (a n b : ℕ) : Prop := b < a ∨ a + n ≤ b

/-- Two regions of the memory, of `n` cells from `a` and of `n'` cells from `a'`, do not meet. -/
abbrev Apart (a n a' n' : ℕ) : Prop := a + n ≤ a' ∨ a' + n' ≤ a

/-- The memory `μ'` agrees with `μ` on every cell that satisfies `K`. -/
def SameOn (K : ℕ → Prop) (μ μ' : ℕ → ℤ) : Prop := ∀ b, K b → μ' b = μ b

/-- No cell below the free pointer has changed. -/
abbrev Kept (μ μ' : ℕ → ℤ) (fr : ℕ) : Prop := SameOn (· < fr) μ μ'

/-- No cell below the free pointer has changed, except the `len` cells from `out`. -/
abbrev KeptBut (μ μ' : ℕ → ℤ) (fr out len : ℕ) : Prop :=
  SameOn (fun x => x < fr ∧ Outside out len x) μ μ'

/-- The cells a, a + 1, … of the memory μ hold the list l. -/
def Seg (μ : ℕ → ℤ) (a : ℕ) (l : List ℤ) : Prop := ∀ i (h : i < l.length), μ (a + i) = l[i]

/-- The cells a, a + 1, … hold a list of natural numbers. -/
abbrev SegN (μ : ℕ → ℤ) (a : ℕ) (l : List ℕ) : Prop := Seg μ a (l.map fun x : ℕ => (x : ℤ))

/-- All members of the list `l` have absolute value at most `U`. -/
def AbsLe (l : List ℤ) (U : ℤ) : Prop := ∀ x ∈ l, |x| ≤ U

/-- What a run needs: the largest absolute value it forms, the number of cells it uses from the free
pointer on, and the number of levels of calls below the procedure. -/
structure Need : Type where
  word : ℕ
  cells : ℕ
  depth : ℕ

/-- The limits allow for the need of a procedure that is called at depth `d` with the free pointer
`fr`.  An address always fits in a word. -/
structure Need.Ok (r : Need) (lim : Limits) (fr d : ℕ) : Prop where
  word : (r.word : ℤ) ≤ lim.word
  cells : fr + r.cells ≤ lim.space
  space : (lim.space : ℤ) ≤ lim.word
  depth : d + r.depth ≤ lim.depth

/-- A need that depends on a size and a bound is polynomially bounded in the two: by
`2^s ((n + 1) (U + 1))^k`. -/
def PolyNeed (need : ℕ → ℕ → Need) : Prop :=
  ∃ s k : ℕ, ∀ n U : ℕ, (need n U).word ≤ polyBound s k [n, U] ∧ (need n U).cells ≤
    polyBound s k [n, U] ∧
    (need n U).depth ≤ polyBound s k [n, U]

/-- A problem with a calling convention. -/
structure Task : Type 1 where
  /-- The instances, as they lie in the memory: sizes, bound, addresses, contents. -/
  Inst : Type
  /-- The size of an instance. -/
  size : Inst → ℕ
  /-- The bound on the absolute values of its numbers that is handed to the solver. -/
  bound : Inst → ℕ
  /-- The arguments of the call, without the free pointer, which comes last. -/
  args : Inst → List ℤ
  /-- The instance is valid, and it lies in the memory below the free pointer. -/
  Pre : Inst → (ℕ → ℤ) → ℕ → Prop
  /-- The result and the final memory are right.  (That the cells below the free pointer are
  otherwise unchanged is part of this.) -/
  Post : Inst → (ℕ → ℤ) → ℕ → ℤ → (ℕ → ℤ) → Prop

/-- **Procedure `p` of the program `P` solves the task** within `T (size) (bound)` steps, whenever
the limits allow for `need (size) (bound)`; and so it does in every program that begins with `P`. -/
def Solves (task : Task) (P : Program) (p : ℕ) (T : ℕ → ℕ → ℕ) (need : ℕ → ℕ → Need) : Prop :=
  ∃ body, P[p]? = some body ∧
    ∀ (R : Program) (lim : Limits) (d : ℕ) (x : task.Inst) (μ : ℕ → ℤ) (fr : ℕ), task.Pre x μ fr →
      (need (task.size x) (task.bound x)).Ok lim fr d →
      Ends lim (P ++ R) d body ⟨frame (task.args x ++ [(fr : ℤ)]), μ⟩
        (T (task.size x) (task.bound x))
        fun σ' => task.Post x μ fr (σ'.loc 0) σ'.mem

/-- "The task is solved in time `T`", for a real-valued `T` whose second argument is an upper bound
on the numbers: some solver with a polynomially bounded need takes at most `T n u` steps on every
instance of size `n ≥ 1` with a bound `1 ≤ U ≤ u`. -/
def SolvedIn (task : Task) (T : ℕ → ℝ → ℝ) : Prop :=
  ∃ (P : Program) (p : ℕ) (Tn : ℕ → ℕ → ℕ) (need : ℕ → ℕ → Need), PolyNeed need ∧
    Solves task P p Tn need ∧
    ∀ (n U : ℕ) (u : ℝ), 1 ≤ n → 1 ≤ U → (U : ℝ) ≤ u → (Tn n U : ℝ) ≤ T n u

/-- A problem with a calling convention and a list of parameters. -/
structure TaskN : Type 1 where
  /-- The instances, as they lie in the memory. -/
  Inst : Type
  /-- The parameters on which time and need depend. -/
  pars : Inst → List ℕ
  /-- The arguments of the call, without the free pointer, which comes last. -/
  args : Inst → List ℤ
  /-- The instance is valid, and it lies in the memory below the free pointer. -/
  Pre : Inst → (ℕ → ℤ) → ℕ → Prop
  /-- The result and the final memory are right. -/
  Post : Inst → (ℕ → ℤ) → ℕ → ℤ → (ℕ → ℤ) → Prop

/-- Procedure `p` of the program `P` solves the task within `T pars` steps, whenever the limits
allow for `need pars`; and so it does in every program that begins with `P`. -/
def SolvesN (task : TaskN) (P : Program) (p : ℕ) (T : List ℕ → ℕ) (need : List ℕ → Need) : Prop :=
  ∃ body, P[p]? = some body ∧
    ∀ (R : Program) (lim : Limits) (d : ℕ) (x : task.Inst) (μ : ℕ → ℤ) (fr : ℕ), task.Pre x μ fr →
      (need (task.pars x)).Ok lim fr d →
      Ends lim (P ++ R) d body ⟨frame (task.args x ++ [(fr : ℤ)]), μ⟩ (T (task.pars x))
        fun σ' => task.Post x μ fr (σ'.loc 0) σ'.mem

/-- A need that is polynomially bounded in the parameters. -/
def PolyNeedN (need : List ℕ → Need) : Prop :=
  ∃ s k : ℕ, ∀ ps : List ℕ, (need ps).word ≤ polyBound s k ps ∧ (need ps).cells ≤ polyBound s k ps ∧
    (need ps).depth ≤ polyBound s k ps

end Lax350013.ProcedureContracts
end

-- Lax350013.WordRAM
section
namespace Lax350013
end Lax350013

namespace Lax350013.WordRAM
end Lax350013.WordRAM

namespace Lax350013.WordRAM.Instr
end Lax350013.WordRAM.Instr

namespace Lax350013.WordRAM.exec
end Lax350013.WordRAM.exec

namespace Lax350013.WordRAM.Instr.accept
end Lax350013.WordRAM.Instr.accept

namespace Lax350013.WordRAM.Instr.add
end Lax350013.WordRAM.Instr.add

namespace Lax350013.WordRAM.Instr.bltz
end Lax350013.WordRAM.Instr.bltz

namespace Lax350013.WordRAM.Instr.load
end Lax350013.WordRAM.Instr.load

namespace Lax350013.WordRAM.Instr.mul
end Lax350013.WordRAM.Instr.mul

namespace Lax350013.WordRAM.Instr.one
end Lax350013.WordRAM.Instr.one

namespace Lax350013.WordRAM.Instr.reject
end Lax350013.WordRAM.Instr.reject

namespace Lax350013.WordRAM.Instr.store
end Lax350013.WordRAM.Instr.store

namespace Lax350013.WordRAM.Instr.sub
end Lax350013.WordRAM.Instr.sub
end

-- Lax350013.PolynomialTime
section
namespace Lax350013.PolynomialTime

open Lax350013.WordRAM

/-- `yes`: when to accept (always, if not given). `output`: a condition on the cells after the input, read as signed. -/
structure Problem where
  Instance : Nat → Type
  input {n : Nat} : Instance n → List Int
  yes {n : Nat} : Instance n → Prop := fun _ => True
  output {n : Nat} : Instance n → (Nat → Int) → Prop := fun _ _ => True

end Lax350013.PolynomialTime
end

-- Lax350013.ThreeSUM
section
namespace Lax350013.ThreeSUM

open Lax350013.PolynomialTime

/-- Section 1: «Given n numbers, decide whether three of them sum to 0». Three different positions. -/
def ThreeSum : Problem where
  Instance n := Fin n → Int
  input x := List.ofFn x
  yes x := ∃ i j k, i ≠ j ∧ j ≠ k ∧ i ≠ k ∧ x i + x j + x k = 0

end Lax350013.ThreeSUM
end

-- Lax350013.CallableProblems
section
namespace Lax350013.CallableProblems

open Finset

open Lax350013.StructuredPrograms

open Lax350013.ProcedureContracts

/-- Section 3.2: "An instance of Exact Triangle [...] consists of a complete tripartite graph on
vertex parts A, B, C of n vertices each, and an integer weight w(e) on every edge".  The three
fields are the weights `w(a,b)`, `w(b,c)` and `w(a,c)`.  The type `R` of the weights is `ℤ` in
Section 3; Section 5 also uses real weights.  The bound on the weights is a separate predicate
(`WeightsBoundedBy`, `WeightsPolyBounded`). -/
structure TriangleInstance (R : Type) (n : ℕ) where
  /-- `wAB a b` is the weight `w(a,b)` of the edge between `a ∈ A` and `b ∈ B`. -/
  wAB : Fin n → Fin n → R
  /-- `wBC b c` is the weight `w(b,c)` of the edge between `b ∈ B` and `c ∈ C`. -/
  wBC : Fin n → Fin n → R
  /-- `wAC a c` is the weight `w(a,c)` of the edge between `a ∈ A` and `c ∈ C`. -/
  wAC : Fin n → Fin n → R

namespace TriangleInstance

/-- Section 3.2: "Let S(a,b,c) := w(a,b) + w(b,c) + w(a,c)." -/
def S {R : Type} [Add R] {n : ℕ} (T : TriangleInstance R n) (a b c : Fin n) : R :=
  T.wAB a b + T.wBC b c + T.wAC a c

/-- Section 3.2: "A zero triangle is a triangle (a,b,c) ∈ A × B × C with S(a,b,c) = 0". -/
def IsZeroTriangle {R : Type} [Add R] [Zero R] {n : ℕ} (T : TriangleInstance R n) (a b c : Fin n) :
    Prop :=
  T.S a b c = 0

/-- Section 3.2: "the task is to decide whether one exists". -/
def HasZeroTriangle {R : Type} [Add R] [Zero R] {n : ℕ} (T : TriangleInstance R n) : Prop :=
  ∃ a b c : Fin n, T.IsZeroTriangle a b c

end TriangleInstance

/-- **Negative Triangle**, Section 1.2: "asks whether an edge-weighted graph has a triangle of
negative total weight".  The instances here are those of Exact Triangle. -/
def TriangleInstance.HasNegativeTriangle {R : Type} [Add R] [Zero R] [LT R] {n : ℕ}
    (T : TriangleInstance R n) : Prop :=
  ∃ a b c : Fin n, T.S a b c < 0

/-- **Convolution-3SUM**, Section 1.2: "do x₀, …, x_{n−1} satisfy x_i + x_j = x_{i+j} for some
i, j?" -/
def Convolution3SUM {R : Type} [Add R] {N : ℕ} (x : Fin N → R) : Prop :=
  ∃ (i j : Fin N) (h : i.val + j.val < N), x i + x j = x ⟨i.val + j.val, h⟩

/-- The vertex at which the walk that starts at `i` and then visits `rest` ends. -/
def walkEnd {n : ℕ} : Fin n → List (Fin n) → Fin n
  | i, [] => i
  | _, j :: rest => walkEnd j rest

/-- The total weight of the walk that starts at `i` and then visits `rest`; it is `⊤` if one of its
edges is missing, and the empty walk has weight 0. -/
def walkWeight {R : Type} [Add R] [Zero R] {n : ℕ} (w : Fin n → Fin n → WithTop R) :
    Fin n → List (Fin n) → WithTop R
  | _, [] => 0
  | i, j :: rest => w i j + walkWeight w j rest

/-- Section 1 and Theorems 21 and 22: "no negative cycles".  Stated for closed walks, which is the
same thing: a closed walk decomposes into cycles. -/
def NoNegativeCycle {R : Type} [Add R] [Zero R] [LE R] {n : ℕ} (w : Fin n → Fin n → WithTop R) :
    Prop :=
  ∀ (i : Fin n) (rest : List (Fin n)), walkEnd i rest = i → 0 ≤ walkWeight w i rest

/-- **APSP**, Section 1: "compute the shortest-path distance between every pair of vertices".  `d i
j` is the least weight of a walk from `i` to `j`, and `⊤` if `j` cannot be reached from `i`. -/
def IsDistanceMatrix {R : Type} [Add R] [Zero R] [Preorder R] {n : ℕ}
    (w : Fin n → Fin n → WithTop R) (d : Fin n → Fin n → WithTop R) : Prop :=
  ∀ i j, IsLeast {x | ∃ rest : List (Fin n), walkEnd i rest = j ∧ walkWeight w i rest = x} (d i j)

abbrev ThreeSum := @Lax350013.ThreeSUM.ThreeSum.yes

/-- The entry `(i, j)` of a matrix with `n` columns that is stored in the list `L`, row by row. -/
abbrev entry (n : ℕ) (L : List ℤ) (i j : ℕ) : ℤ := L.getD (i * n + j) 0

/-- The `N` numbers in a list. -/
def vecOf (N : ℕ) (x : List ℤ) : Fin N → ℤ := fun i => x.getD i 0

/-- The complete tripartite graph with `n` vertices per part whose three weight matrices are in
three lists, row by row: the weight of `(a, b)` at `a n + b` of the first, of `(b, c)` at `b n + c`
of the second, of `(a, c)` at `a n + c` of the third. -/
def triOf (n : ℕ) (AB BC AC : List ℤ) : TriangleInstance ℤ n where
  wAB a b := AB.getD (a * n + b) 0
  wBC b c := BC.getD (b * n + c) 0
  wAC a c := AC.getD (a * n + c) 0

/-- The weight matrix of a directed graph on `n` vertices: the weight of the edge `(i, j)` is in
cell `i n + j` of `w` if cell `i n + j` of `adj` holds 1, and there is no edge otherwise. -/
def graphOf (n : ℕ) (adj w : List ℤ) : Fin n → Fin n → WithTop ℤ := fun i j =>
  if adj.getD (i * n + j) 0 = 1 then ((w.getD (i * n + j) 0 : ℤ) : WithTop ℤ) else ⊤

/-- The smallest of `A[i,k] + B[k,j]` over `k < n`, by one pass, for `n ≥ 1`. -/
def minPlusEntry (n : ℕ) (A B : List ℤ) (i j : ℕ) : ℤ :=
  (List.range (n - 1)).foldl
    (fun acc k => min acc (entry n A i (k + 1) + entry n B (k + 1) j))
    (entry n A i 0 + entry n B 0 j)

/-- The (min,+)-product of two `n × n` matrices, row by row. -/
def minPlusList (n : ℕ) (A B : List ℤ) : List ℤ :=
  (List.range (n * n)).map fun q => minPlusEntry n A B (q / n) (q % n)

open Classical in
/-- The answer of a decision problem as a number: 1 for yes, 0 for no. -/
noncomputable def flag (p : Prop) : ℤ := if p then 1 else 0

/-- Three `n × n` matrices of weights in the memory. -/
structure TriInst : Type where
  n : ℕ
  U : ℕ
  ab : ℕ
  bc : ℕ
  ac : ℕ
  AB : List ℤ
  BC : List ℤ
  AC : List ℤ

/-- The three matrices lie below the free pointer, and their entries are bounded by `U`. -/
structure TriInst.Pre (x : TriInst) (μ : ℕ → ℤ) (fr : ℕ) : Prop where
  n_pos : 1 ≤ x.n
  U_pos : 1 ≤ x.U
  lenAB : x.AB.length = x.n * x.n
  lenBC : x.BC.length = x.n * x.n
  lenAC : x.AC.length = x.n * x.n
  segAB : Seg μ x.ab x.AB
  segBC : Seg μ x.bc x.BC
  segAC : Seg μ x.ac x.AC
  leAB : AbsLe x.AB x.U
  leBC : AbsLe x.BC x.U
  leAC : AbsLe x.AC x.U
  belowAB : x.ab + x.n * x.n ≤ fr
  belowBC : x.bc + x.n * x.n ≤ fr
  belowAC : x.ac + x.n * x.n ≤ fr

/-- **Exact Triangle**: et(n, U, ab, bc, ac, fr) returns 1 if there is a zero triangle and 0 if not.
-/
noncomputable def etTask : Task where
  Inst := TriInst
  size x := x.n
  bound x := x.U
  args x := [x.n, x.U, x.ab, x.bc, x.ac]
  Pre := TriInst.Pre
  Post x μ fr r μ' := r = flag (triOf x.n x.AB x.BC x.AC).HasZeroTriangle ∧ Kept μ μ' fr

/-- **Negative Triangle**: nt(n, U, ab, bc, ac, fr) returns 1 if there is a negative triangle and 0
if not. -/
noncomputable def ntTask : Task where
  Inst := TriInst
  size x := x.n
  bound x := x.U
  args x := [x.n, x.U, x.ab, x.bc, x.ac]
  Pre := TriInst.Pre
  Post x μ fr r μ' := r = flag (triOf x.n x.AB x.BC x.AC).HasNegativeTriangle ∧ Kept μ μ' fr

/-- A list of `N` numbers in the memory. -/
structure VecInst : Type where
  N : ℕ
  U : ℕ
  a : ℕ
  X : List ℤ

/-- The list lies below the free pointer, and its entries are bounded by `U`. -/
structure VecInst.Pre (x : VecInst) (μ : ℕ → ℤ) (fr : ℕ) : Prop where
  N_pos : 1 ≤ x.N
  U_pos : 1 ≤ x.U
  len : x.X.length = x.N
  seg : Seg μ x.a x.X
  le : AbsLe x.X x.U
  below : x.a + x.N ≤ fr

/-- **Convolution-3SUM**: c3(N, U, x, fr) returns 1 if `x_i + x_j = x_{i+j}` for some `i`, `j`, and
0 if not. -/
noncomputable def c3Task : Task where
  Inst := VecInst
  size x := x.N
  bound x := x.U
  args x := [x.N, x.U, x.a]
  Pre := VecInst.Pre
  Post x μ fr r μ' := r = flag (Convolution3SUM (vecOf x.N x.X)) ∧ Kept μ μ' fr

/-- **3SUM**: s3(n, U, x, fr) returns 1 if three of the numbers, at different positions, sum to 0,
and 0 if not. -/
noncomputable def s3Task : Task where
  Inst := VecInst
  size x := x.N
  bound x := x.U
  args x := [x.N, x.U, x.a]
  Pre := VecInst.Pre
  Post x μ fr r μ' := r = flag (ThreeSum (vecOf x.N x.X)) ∧ Kept μ μ' fr

/-- Two `n × n` matrices in the memory, and the place for a third. -/
structure MatInst : Type where
  n : ℕ
  U : ℕ
  a : ℕ
  b : ℕ
  c : ℕ
  A : List ℤ
  B : List ℤ

/-- The two matrices and the place for the product lie below the free pointer; the place for the
product does not meet the two matrices. -/
structure MatInst.Pre (x : MatInst) (μ : ℕ → ℤ) (fr : ℕ) : Prop where
  n_pos : 1 ≤ x.n
  U_pos : 1 ≤ x.U
  lenA : x.A.length = x.n * x.n
  lenB : x.B.length = x.n * x.n
  segA : Seg μ x.a x.A
  segB : Seg μ x.b x.B
  leA : AbsLe x.A x.U
  leB : AbsLe x.B x.U
  belowA : x.a + x.n * x.n ≤ fr
  belowB : x.b + x.n * x.n ≤ fr
  belowC : x.c + x.n * x.n ≤ fr
  apartA : Apart x.a (x.n * x.n) x.c (x.n * x.n)
  apartB : Apart x.b (x.n * x.n) x.c (x.n * x.n)

/-- **The (min,+)-product**: mp(n, U, a, b, c, fr) writes the product of the matrices at `a` and `b`
to `c`. -/
def mpTask : Task where
  Inst := MatInst
  size x := x.n
  bound x := x.U
  args x := [x.n, x.U, x.a, x.b, x.c]
  Pre := MatInst.Pre
  Post x μ fr _ μ' := Seg μ' x.c (minPlusList x.n x.A x.B) ∧ KeptBut μ μ' fr x.c (x.n * x.n)

/-- A directed graph in the memory: adjacency matrix and weights, and the place for the `2n²` cells
of the answer. -/
structure GraphInst : Type where
  n : ℕ
  U : ℕ
  adj : ℕ
  w : ℕ
  out : ℕ
  ADJ : List ℤ
  W : List ℤ

/-- The graph and the place for the answer lie below the free pointer; the graph has no negative
cycle. -/
structure GraphInst.Pre (x : GraphInst) (μ : ℕ → ℤ) (fr : ℕ) : Prop where
  n_pos : 1 ≤ x.n
  U_pos : 1 ≤ x.U
  lenADJ : x.ADJ.length = x.n * x.n
  lenW : x.W.length = x.n * x.n
  segADJ : Seg μ x.adj x.ADJ
  segW : Seg μ x.w x.W
  zeroOne : ∀ e ∈ x.ADJ, e = 0 ∨ e = 1
  leW : AbsLe x.W x.U
  belowADJ : x.adj + x.n * x.n ≤ fr
  belowW : x.w + x.n * x.n ≤ fr
  belowOut : x.out + 2 * (x.n * x.n) ≤ fr
  apartADJ : Apart x.adj (x.n * x.n) x.out (2 * (x.n * x.n))
  apartW : Apart x.w (x.n * x.n) x.out (2 * (x.n * x.n))
  noNegativeCycle : NoNegativeCycle (graphOf x.n x.ADJ x.W)

/-- **APSP**: ap(n, U, adj, w, out, fr) writes two cells for each pair `(i, j)`, at
`out + 2 (i n + j)`: 1 and the distance from `i` to `j` if `j` can be reached from `i`, and 0 in the
first cell if not. -/
def apTask : Task where
  Inst := GraphInst
  size x := x.n
  bound x := x.U
  args x := [x.n, x.U, x.adj, x.w, x.out]
  Pre := GraphInst.Pre
  Post x μ fr _ μ' :=
    (∃ dist : Fin x.n → Fin x.n → WithTop ℤ, IsDistanceMatrix (graphOf x.n x.ADJ x.W) dist ∧
    ∀ i j : Fin x.n,
      (dist i j = ⊤ → μ' (x.out + 2 * (i.val * x.n + j.val)) = 0) ∧
      ∀ z : ℤ, dist i j = (z : WithTop ℤ) →
        μ' (x.out + 2 * (i.val * x.n + j.val)) = 1 ∧
          μ' (x.out + 2 * (i.val * x.n + j.val) + 1) = z) ∧
    KeptBut μ μ' fr x.out (2 * (x.n * x.n))

/-- Matrices `X` (`N × D`) and `Y` (`D × N`), row by row, `w` wanted positions (rows in `WI`,
columns in `WJ`), and the place for `w` answers. -/
structure ThinInst : Type where
  /-- The number of rows of `X` and of columns of `Y`. -/
  N : ℕ
  /-- The number of columns of `X` and of rows of `Y`. -/
  D : ℕ
  /-- The number of wanted positions. -/
  w : ℕ
  /-- The bound on the absolute values of the entries. -/
  U : ℕ
  /-- The address of `X`. -/
  x : ℕ
  /-- The address of `Y`. -/
  y : ℕ
  /-- The address of `WI`. -/
  wi : ℕ
  /-- The address of `WJ`. -/
  wj : ℕ
  /-- The address of the answers. -/
  out : ℕ
  /-- The first matrix, row by row. -/
  X : List ℤ
  /-- The second matrix, row by row. -/
  Y : List ℤ
  /-- The rows of the wanted positions. -/
  WI : List ℕ
  /-- The columns of the wanted positions. -/
  WJ : List ℕ

/-- Everything lies below the free pointer, the entries are bounded by `U`, the positions are
distinct positions of an `N × N` matrix, and the place for the answers meets none of the inputs. -/
structure ThinInst.Pre (x : ThinInst) (μ : ℕ → ℤ) (fr : ℕ) : Prop where
  N_pos : 1 ≤ x.N
  D_pos : 1 ≤ x.D
  U_pos : 1 ≤ x.U
  lenX : x.X.length = x.N * x.D
  lenY : x.Y.length = x.D * x.N
  lenWI : x.WI.length = x.w
  lenWJ : x.WJ.length = x.w
  segX : Seg μ x.x x.X
  segY : Seg μ x.y x.Y
  segWI : SegN μ x.wi x.WI
  segWJ : SegN μ x.wj x.WJ
  leX : AbsLe x.X x.U
  leY : AbsLe x.Y x.U
  ltWI : ∀ i ∈ x.WI, i < x.N
  ltWJ : ∀ j ∈ x.WJ, j < x.N
  nodup : (x.WI.zip x.WJ).Nodup
  belowX : x.x + x.N * x.D ≤ fr
  belowY : x.y + x.D * x.N ≤ fr
  belowWI : x.wi + x.w ≤ fr
  belowWJ : x.wj + x.w ≤ fr
  belowOut : x.out + x.w ≤ fr
  apartX : Apart x.out x.w x.x (x.N * x.D)
  apartY : Apart x.out x.w x.y (x.D * x.N)
  apartWI : Apart x.out x.w x.wi x.w
  apartWJ : Apart x.out x.w x.wj x.w

/-- The entries of both matrices are 0 or 1. -/
def ThinInst.ZeroOne (x : ThinInst) : Prop := (∀ v ∈ x.X, v = 0 ∨ v = 1) ∧ ∀ v ∈ x.Y, v = 0 ∨ v = 1

/-- The entry `(XY)[I, J]`. -/
def thinEntry (N D : ℕ) (X Y : List ℤ) (I J : ℕ) : ℤ :=
  ((List.range D).map fun k => X.getD (I * D + k) 0 * Y.getD (k * N + J) 0).sum

/-- The wanted entries, in the order of the positions. -/
def thinOut (N D : ℕ) (X Y : List ℤ) (WI WJ : List ℕ) : List ℤ :=
  (WI.zip WJ).map fun q => thinEntry N D X Y q.1 q.2

/-- **The wanted entries of a thin matrix product** (Theorem 5, Corollary 26):
`thin(N, D, w, U, x, y, wi, wj, out, fr)`. -/
def thinTask : TaskN where
  Inst := ThinInst
  pars x := [x.N, x.D, x.w, x.U]
  args x := [x.N, x.D, x.w, x.U, x.x, x.y, x.wi, x.wj, x.out]
  Pre := ThinInst.Pre
  Post x μ fr _ μ' := Seg μ' x.out (thinOut x.N x.D x.X x.Y x.WI x.WJ) ∧ KeptBut μ μ' fr x.out x.w

/-- **#Lop-AE-SparseTri** (Definition 14), the graph given by its two biadjacency matrices: the same
call with `U = 1` on matrices of zeros and ones; the answers are the numbers of common
neighbours. -/
def lopCountTask : TaskN where
  Inst := ThinInst
  pars x := [x.N, x.D, x.w]
  args x := [x.N, x.D, x.w, x.U, x.x, x.y, x.wi, x.wj, x.out]
  Pre x μ fr := x.Pre μ fr ∧ x.ZeroOne ∧ x.U = 1
  Post x μ fr _ μ' := Seg μ' x.out (thinOut x.N x.D x.X x.Y x.WI x.WJ) ∧ KeptBut μ μ' fr x.out x.w

/-- **Lop-AE-SparseTri** (Definition 13): the answer is 1 if the pair has a common neighbour and 0
if not. -/
def lopDetectTask : TaskN where
  Inst := ThinInst
  pars x := [x.N, x.D, x.w]
  args x := [x.N, x.D, x.w, x.U, x.x, x.y, x.wi, x.wj, x.out]
  Pre x μ fr := x.Pre μ fr ∧ x.ZeroOne ∧ x.U = 1
  Post x μ fr _ μ' :=
    Seg μ' x.out ((thinOut x.N x.D x.X x.Y x.WI x.WJ).map fun v => if v = 0 then 0 else 1) ∧
      KeptBut μ μ' fr x.out x.w

/-- "The thin matrix product is solved in time `T N D w' u`", where `w'` is an upper bound on the
number `w` of wanted positions and `u` one on the bound `U`. -/
def ThinSolvedIn (T : ℕ → ℕ → ℕ → ℝ → ℝ) : Prop :=
  ∃ (P : Program) (p : ℕ) (Tn : List ℕ → ℕ) (need : List ℕ → Need), PolyNeedN need ∧
    SolvesN thinTask P p Tn need ∧
    ∀ (N D w w' U : ℕ) (u : ℝ), 1 ≤ N → 1 ≤ D → 1 ≤ U → w ≤ w' → (U : ℝ) ≤ u →
      (Tn [N, D, w, U] : ℝ) ≤ T N D w' u

/-- "The task (one of the two lopsided triangle problems) is solved in time `T n D w'`", where `w'`
is an upper bound on the number `w` of query pairs. -/
def LopSolvedIn (task : TaskN) (T : ℕ → ℕ → ℕ → ℝ) : Prop :=
  ∃ (P : Program) (p : ℕ) (Tn : List ℕ → ℕ) (need : List ℕ → Need), PolyNeedN need ∧
    SolvesN task P p Tn need ∧
    ∀ (n D w w' : ℕ), 1 ≤ n → 1 ≤ D → w ≤ w' → (Tn [n, D, w] : ℝ) ≤ T n D w'

end Lax350013.CallableProblems
end

-- Lax350013.CallableAlgorithms
section
namespace Lax350013.CallableAlgorithms

open Finset

open Lax350013.StructuredPrograms

open Lax350013.ProcedureContracts

open Lax350013.CallableProblems

open Filter Asymptotics

/-- Proof of Theorem 19, by Theorem 5: "Let D be the largest power of four with D ≤
n^{1/18}". -/
noncomputable def paramD₅ (n : ℕ) : ℕ := 4 ^ Nat.log 4 ⌊(n : ℝ) ^ (1 / 18 : ℝ)⌋₊

/-- An interpretation of "a deterministic algorithm solves the problem in time T", for each problem
of Sections 2 to 4. Each field is a predicate on running times.  The intended meaning of
`M.problem T`: there is a deterministic algorithm that gives a correct answer on every input, and
that takes time at most `T(parameters)` on every input with these parameters (sizes and `D` as
given, at most `w` pairs, numbers at most `u`; sizes and `u` at least 1). -/
structure DetTimeModel where
  /-- Theorem 5: given `X ∈ ℤ^{N×D}`, `Y ∈ ℤ^{D×N}` with entries of absolute value at most
  `u` and a set of at most `w` positions, compute the wanted entries of `XY` (`IsWantedEntries`).
  The arguments of the time are `N D w u`. -/
  thinProduct : (ℕ → ℕ → ℕ → ℝ → ℝ) → Prop
  /-- #Lop-AE-SparseTri(n, D), Definition 14, with at most `w` query pairs
  (`LopInstance.IsCountingAnswer`).  The arguments of the time are `n D w`. -/
  lopCount : (ℕ → ℕ → ℕ → ℝ) → Prop
  /-- Lop-AE-SparseTri(n, D), Definition 13, with at most `w` query pairs
  (`LopInstance.IsDetectionAnswer`).  The arguments of the time are `n D w`. -/
  lopDetect : (ℕ → ℕ → ℕ → ℝ) → Prop
  /-- Exact Triangle on `n` vertices per part with integer weights of absolute value at most `u`
  (`TriangleInstance.HasZeroTriangle`).  The arguments of the time are `n u`. -/
  exactTriangle : (ℕ → ℝ → ℝ) → Prop
  /-- Negative Triangle, decision (`TriangleInstance.HasNegativeTriangle`).  Arguments `n u`. -/
  negativeTriangle : (ℕ → ℝ → ℝ) → Prop
  /-- Convolution-3SUM on `N` integers of absolute value at most `u` (`Convolution3SUM`).  Arguments
  `N u`. -/
  convolution3SUM : (ℕ → ℝ → ℝ) → Prop
  /-- 3SUM on `n` integers of absolute value at most `u` (`ThreeSum`).  Arguments `n u`. -/
  threeSum : (ℕ → ℝ → ℝ) → Prop
  /-- The (min,+)-product of two `n × n` integer matrices with entries of absolute value at most `u`
  (`IsMinPlusProduct`). Arguments `n u`. -/
  minPlusProduct : (ℕ → ℝ → ℝ) → Prop
  /-- APSP on directed `n`-vertex graphs with integer weights of absolute value at most `u` and no
  negative cycles (`IsDistanceMatrix`, `NoNegativeCycle`).  Arguments `n u`. -/
  apsp : (ℕ → ℝ → ℝ) → Prop

/-- The bound of Theorem 5 and of the first case of Corollary 15: `n² log² D / D^{1/18}`. -/
noncomputable abbrev thinBound (n D : ℕ) : ℝ :=
  (n : ℝ) ^ 2 * Real.log D ^ 2 / (D : ℝ) ^ (1 / 18 : ℝ)

namespace Closure

end Closure

namespace Claim

/-- **Corollary 15**, the first case: "Let D ≥ 4 be a power of four with n ≥ D^18, and
consider an instance of #Lop-AE-SparseTri(n,D) or of Lop-AE-SparseTri(n,D) with |W| query pairs.
If |W| ≤ n²/√D, then the instance can be solved deterministically in O(n² log² D/D^{1/18}) time."
`Tc` is the time for the counting problem, `Td` for the detection problem. -/
def Corollary_15_first (M : DetTimeModel) : Prop :=
  ∃ (C : ℝ) (Tc Td : ℕ → ℕ → ℕ → ℝ), 0 ≤ C ∧ M.lopCount Tc ∧ M.lopDetect Td ∧
    ∀ n D w : ℕ, (∃ k : ℕ, D = 4 ^ k) → 4 ≤ D → D ^ 18 ≤ n → (w : ℝ) ≤ (n : ℝ) ^ 2 / Real.sqrt D →
      Tc n D w ≤ C * thinBound n D ∧ Td n D w ≤ C * thinBound n D

end Claim

/-- The reading of "is solved in time T" by programs of the light language. -/
noncomputable def lightModel : DetTimeModel where
  thinProduct := ThinSolvedIn
  lopCount := LopSolvedIn lopCountTask
  lopDetect := LopSolvedIn lopDetectTask
  exactTriangle := SolvedIn etTask
  negativeTriangle := SolvedIn ntTask
  convolution3SUM := SolvedIn c3Task
  threeSum := SolvedIn s3Task
  minPlusProduct := SolvedIn mpTask
  apsp := SolvedIn apTask

end Lax350013.CallableAlgorithms
end

-- Lax350013.RAMResources
section
namespace Lax350013.RAMResources
end Lax350013.RAMResources

namespace Lax350013.RAMResources.Problem
end Lax350013.RAMResources.Problem

namespace Lax350013.RAMResources.RunsPhases
end Lax350013.RAMResources.RunsPhases

namespace Lax350013.RAMResources.Serves
end Lax350013.RAMResources.Serves
end

-- Lax350013.ThinMatrices
section
namespace Lax350013.ThinMatrices
end Lax350013.ThinMatrices

namespace Lax350013.ThinMatrices.ThinInstance
end Lax350013.ThinMatrices.ThinInstance

namespace Lax350013.ThinMatrices.ThinPair
end Lax350013.ThinMatrices.ThinPair
end

-- Lax350013.LopsidedTriangles
section
namespace Lax350013.LopsidedTriangles.ThinInstance
end Lax350013.LopsidedTriangles.ThinInstance

namespace Lax350013.LopsidedTriangles

open Finset

open Lax350013.WordRAM

open Lax350013.RAMResources

open Lax350013.ThinMatrices

/-- **Definition 13**, the input: "an unweighted undirected tripartite graph with two parts
A and B of n vertices each and a middle part M [...], with arbitrary edges in M × A and M × B.  Let
W ⊆ A × B be the set of edges between A and B."  The bound "of at most D vertices" on the middle
part is `LopInstance.MiddleAtMost`. -/
structure LopInstance (n : ℕ) where
  /-- The middle part `M`. -/
  M : Type
  /-- The middle part is finite. -/
  [fintypeM : Fintype M]
  /-- `adjA a v`: the vertex `a ∈ A` and the middle vertex `v ∈ M` are adjacent. -/
  adjA : Fin n → M → Prop
  /-- `adjB v b`: the middle vertex `v ∈ M` and the vertex `b ∈ B` are adjacent. -/
  adjB : M → Fin n → Prop
  /-- The set `W ⊆ A × B` of edges between `A` and `B`; Section 3.1 calls its elements the query
  pairs. -/
  W : Finset (Fin n × Fin n)

attribute [instance] LopInstance.fintypeM

end Lax350013.LopsidedTriangles
end

-- Lax350013.LopsidedTriangleAlgorithms
section
namespace Lax350013.LopsidedTriangleAlgorithms

open Finset

open Lax350013.WordRAM

open Lax350013.RAMResources

open Lax350013.ThinMatrices

open Lax350013.LopsidedTriangles

/-- Callable contract proved by upstream `Light.Sec3.claim_corollary_15_first`. -/
axiom callableCorollary15First : Lax350013.CallableAlgorithms.Claim.Corollary_15_first Lax350013.CallableAlgorithms.lightModel

end Lax350013.LopsidedTriangleAlgorithms
end
