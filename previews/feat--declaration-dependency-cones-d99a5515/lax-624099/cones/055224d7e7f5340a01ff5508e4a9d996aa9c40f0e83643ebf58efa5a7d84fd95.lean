-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Computability.PartrecCode
import Mathlib.ModelTheory.Complexity
import Mathlib.ModelTheory.Order
import Mathlib.ModelTheory.Semantics
import Mathlib.Tactic.FinCases

-- Lax904597.Problems
section
namespace Lax904597.Problems

open FirstOrder FirstOrder.Language

/-- A decision problem: an isomorphism-closed property of `L`-structures,
whose yes-instances are the `L`-structures satisfying it. -/
structure DecisionProblem (L : Language.{0, 0}) [L.IsRelational] where
  /-- The predicate: `P A` (through the function coercion) states that the
  structure `A` is a yes-instance. -/
  Holds : ∀ (A : Type) [L.Structure A], Prop
  /-- Decision problems do not distinguish isomorphic structures. -/
  iso_invariant : ∀ {A B : Type} [L.Structure A] [L.Structure B],
    (A ≃[L] B) → (Holds A ↔ Holds B)

namespace DecisionProblem

variable {L : Language.{0, 0}} [L.IsRelational]

end DecisionProblem

end Lax904597.Problems
end

-- Lax624099.Problems
section
namespace Lax624099.Problems

open FirstOrder FirstOrder.Language Lax904597.Problems

/-- The decision problem whose yes-instances are the structures isomorphic to
one satisfying `P`. -/
def DecisionProblem.ofPred {L : Language.{0, 0}} [L.IsRelational]
    (P : ∀ (A : Type) [L.Structure A], Prop) : DecisionProblem L where
  Holds := fun A _ => ∃ (B : Type) (i : L.Structure B) (_ : @Language.Equiv L B A i _), @P B i
  iso_invariant := fun e =>
    ⟨fun ⟨B, i, f, h⟩ => ⟨B, i, e.comp f, h⟩, fun ⟨B, i, f, h⟩ => ⟨B, i, e.symm.comp f, h⟩⟩

end Lax624099.Problems
end

-- Lax904597.Interpretations
section
namespace Lax904597.Interpretations
end Lax904597.Interpretations

namespace Lax904597.Interpretations.FOInterpretation
end Lax904597.Interpretations.FOInterpretation

namespace Lax904597.Interpretations.FOReduction
end Lax904597.Interpretations.FOReduction

namespace Lax904597.Interpretations.OrderedFOReduction
end Lax904597.Interpretations.OrderedFOReduction
end

-- Lax904597.Relativized
section
namespace Lax904597.Relativized
end Lax904597.Relativized

namespace Lax904597.Relativized.RelFOInterpretation
end Lax904597.Relativized.RelFOInterpretation

namespace Lax904597.Relativized.RelOrderedFOReduction
end Lax904597.Relativized.RelOrderedFOReduction
end

-- Lax904597.SecondOrder
section
namespace Lax904597.SecondOrder.SORealize
end Lax904597.SecondOrder.SORealize

namespace Lax904597.SecondOrder.soLang
end Lax904597.SecondOrder.soLang

namespace Lax904597.SecondOrder

open FirstOrder FirstOrder.Language Lax904597.Problems

/-- A second-order quantifier block: finitely many relation variables, with
given arities. The index type is arbitrary rather than an initial segment of
`ℕ`, so that constructions on blocks can build their natural index types. -/
structure SOBlock : Type 1 where
  /-- The index type of the relation variables of the block. -/
  ι : Type
  /-- A block has finitely many relation variables. -/
  [ιFinite : Finite ι]
  /-- The arity of each relation variable. -/
  arity : ι → ℕ

attribute [instance] SOBlock.ιFinite

variable {L : Language.{0, 0}}

end Lax904597.SecondOrder
end

-- Lax904597.Classes
section
namespace Lax904597.Classes
end Lax904597.Classes

namespace Lax904597.Classes.ComplexityClass
end Lax904597.Classes.ComplexityClass
end

-- Lax624099.CodeHalting
section
namespace Lax624099.CodeHalting

open FirstOrder

open FirstOrder.Language

/-- Relation symbols of code instances. -/
inductive codeRel : ℕ → Type
  /-- `croot n`: `n` is the root of the syntax tree. -/
  | croot : codeRel 1
  /-- `czero n`: `n` draws the constructor `zero`. -/
  | czero : codeRel 1
  /-- `csucc n`: `n` draws the constructor `succ`. -/
  | csucc : codeRel 1
  /-- `cleft n`: `n` draws the constructor `left`. -/
  | cleft : codeRel 1
  /-- `cright n`: `n` draws the constructor `right`. -/
  | cright : codeRel 1
  /-- `cpair n`: `n` draws the constructor `pair`. -/
  | cpair : codeRel 1
  /-- `ccomp n`: `n` draws the constructor `comp`. -/
  | ccomp : codeRel 1
  /-- `cprec n`: `n` draws the constructor `prec`. -/
  | cprec : codeRel 1
  /-- `crfind n`: `n` draws the constructor `rfind'`. -/
  | crfind : codeRel 1
  /-- `carg1 n m`: `m` is the first child of `n`. -/
  | carg1 : codeRel 2
  /-- `carg2 n m`: `m` is the second child of `n`. -/
  | carg2 : codeRel 2
  deriving DecidableEq

/-- The relational language of code instances: the eight constructor marks,
the mark of the root, and the two child relations. -/
def code : Language :=
  ⟨fun _ => Empty, codeRel⟩

instance instIsRelationalCode : IsRelational code :=
  fun _ => ⟨fun f => Empty.elim f⟩

/-- The root symbol. -/
abbrev cRoot : code.Relations 1 := .croot

/-- The `zero` symbol. -/
abbrev cZero : code.Relations 1 := .czero

/-- The `succ` symbol. -/
abbrev cSucc : code.Relations 1 := .csucc

/-- The `left` symbol. -/
abbrev cLeft : code.Relations 1 := .cleft

/-- The `right` symbol. -/
abbrev cRight : code.Relations 1 := .cright

/-- The `pair` symbol. -/
abbrev cPair : code.Relations 1 := .cpair

/-- The `comp` symbol. -/
abbrev cComp : code.Relations 1 := .ccomp

/-- The `prec` symbol. -/
abbrev cPrec : code.Relations 1 := .cprec

/-- The `rfind'` symbol. -/
abbrev cRfind : code.Relations 1 := .crfind

/-- The first-child symbol. -/
abbrev cArg1 : code.Relations 2 := .carg1

/-- The second-child symbol. -/
abbrev cArg2 : code.Relations 2 := .carg2

open FirstOrder

open Language Structure

section Shorthands

variable {A : Type} [code.Structure A]

/-- Being the root. -/
def CRoot (a : A) : Prop := RelMap cRoot ![a]

/-- Drawing the constructor `zero`. -/
def CZero (a : A) : Prop := RelMap cZero ![a]

/-- Drawing the constructor `succ`. -/
def CSucc (a : A) : Prop := RelMap cSucc ![a]

/-- Drawing the constructor `left`. -/
def CLeft (a : A) : Prop := RelMap cLeft ![a]

/-- Drawing the constructor `right`. -/
def CRight (a : A) : Prop := RelMap cRight ![a]

/-- Drawing the constructor `pair`. -/
def CPair (a : A) : Prop := RelMap cPair ![a]

/-- Drawing the constructor `comp`. -/
def CComp (a : A) : Prop := RelMap cComp ![a]

/-- Drawing the constructor `prec`. -/
def CPrec (a : A) : Prop := RelMap cPrec ![a]

/-- Drawing the constructor `rfind'`. -/
def CRfind (a : A) : Prop := RelMap cRfind ![a]

/-- Being the first child. -/
def CArg1 (a b : A) : Prop := RelMap cArg1 ![a, b]

/-- Being the second child. -/
def CArg2 (a b : A) : Prop := RelMap cArg2 ![a, b]

end Shorthands

section Decode

variable {A : Type} [code.Structure A]

/-- **The node `n` draws the code `c`.** A recursion on the code: the mark of
the node must be the constructor's, and its children must draw the
constructor's arguments. -/
def DecodesTo (n : A) : Nat.Partrec.Code → Prop
  | .zero => CZero n
  | .succ => CSucc n
  | .left => CLeft n
  | .right => CRight n
  | .pair cf cg =>
      CPair n ∧ ∃ a b, CArg1 n a ∧ CArg2 n b ∧ DecodesTo a cf ∧ DecodesTo b cg
  | .comp cf cg =>
      CComp n ∧ ∃ a b, CArg1 n a ∧ CArg2 n b ∧ DecodesTo a cf ∧ DecodesTo b cg
  | .prec cf cg =>
      CPrec n ∧ ∃ a b, CArg1 n a ∧ CArg2 n b ∧ DecodesTo a cf ∧ DecodesTo b cg
  | .rfind' cf => CRfind n ∧ ∃ a, CArg1 n a ∧ DecodesTo a cf

end Decode

open Lax904597.Problems Lax624099.Problems

/-- The root of the instance draws a code halting on `0`. -/
def CodeHaltsOn (A : Type) [code.Structure A] : Prop :=
  ∃ (n : A) (c : Nat.Partrec.Code), CRoot n ∧ DecodesTo n c ∧ (Nat.Partrec.Code.eval c 0).Dom

/-- CODEHALT: does the partial recursive code drawn in the instance halt on
`0`? -/
def CODEHALT : DecisionProblem code :=
  DecisionProblem.ofPred CodeHaltsOn

end Lax624099.CodeHalting
end
