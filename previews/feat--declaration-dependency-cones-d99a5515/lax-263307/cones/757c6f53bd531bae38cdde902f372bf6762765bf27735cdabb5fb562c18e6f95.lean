-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.DeriveFintype

-- Lax263307.WeightedIndependentSet
section
namespace Lax263307.WeightedIndependentSet

/-- A finite graph with rational vertex weights. -/
structure Instance where
  order : ℕ
  graph : SimpleGraph (Fin order)
  weights : Fin order → ℚ

end Lax263307.WeightedIndependentSet
end

-- Lax560851.StructuralPresentation
section
namespace Lax560851.StructuralPresentation.Raw.nodes
end Lax560851.StructuralPresentation.Raw.nodes

namespace Lax560851.StructuralPresentation

universe u

/-- The universal shape of structurally finite data. -/
inductive Raw where
  | nat : Nat → Raw
  | pair : Raw → Raw → Raw
  deriving DecidableEq

namespace Raw

end Raw

/-- An encoder into the universal shape and a partial inverse. -/
structure Presentation (α : Type u) where
  toRaw : α → Raw
  fromRaw : Raw → Option α

/-- Package an injective structural map as a low-level presentation by
choosing a preimage on its range. This construction certifies no complexity
or constructor-structurality property of the supplied map. -/
noncomputable def presentationOf {α : Type u} (f : α → Raw) : Presentation α := by
  classical
  exact {
    toRaw := f
    fromRaw := fun raw =>
      if h : ∃ x, f x = raw then some (Classical.choose h) else none
  }

namespace Presentation

/-- Distinct values have distinct structural representations. -/
def Faithful {α : Type u} (P : Presentation α) : Prop :=
  Function.Injective P.toRaw

end Presentation

end Lax560851.StructuralPresentation
end

-- Lax560851.StructuralCombinators
section
namespace Lax560851.StructuralCombinators.Derivable
end Lax560851.StructuralCombinators.Derivable

namespace Lax560851.StructuralCombinators.Generated
end Lax560851.StructuralCombinators.Generated

namespace Lax560851.StructuralCombinators.Lawful
end Lax560851.StructuralCombinators.Lawful

namespace Lax560851.StructuralCombinators.SizeLaws
end Lax560851.StructuralCombinators.SizeLaws

namespace Lax560851.StructuralCombinators.listFromRaw
end Lax560851.StructuralCombinators.listFromRaw

namespace Lax560851.StructuralCombinators.prod
end Lax560851.StructuralCombinators.prod

namespace Lax560851.StructuralCombinators.Raw.constructorCharsCode
end Lax560851.StructuralCombinators.Raw.constructorCharsCode

namespace Lax560851.StructuralCombinators.Raw.fields
end Lax560851.StructuralCombinators.Raw.fields

namespace Lax560851.StructuralCombinators

open Lax560851.StructuralPresentation

open Lax560851.StructuralPresentation.Presentation

universe u v

namespace Raw

end Raw

/-- Structural presentation of natural numbers. -/
def nat : Presentation Nat where
  toRaw := .nat
  fromRaw
    | .nat n => some n
    | _ => none

/-- Universal structural representation of a list. -/
def listToRaw {α : Type u} (P : Presentation α) : List α → StructuralPresentation.Raw
  | [] => .nat 0
  | x :: xs => .pair (P.toRaw x) (listToRaw P xs)

end Lax560851.StructuralCombinators
end

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

-- Lax263307.IndependentSetEncoding
section
namespace Lax263307.IndependentSetEncoding

open WeightedIndependentSet

open Lax560851.StructuralPresentation Lax560851.StructuralCombinators

open Lax759944.BinaryWordEncoding (bitSize)

open scoped Classical

/-- Canonical sign, absolute numerator, and denominator of a rational. -/
def encodeRational (q : ℚ) : List ℕ :=
  [if q.num < 0 then 1 else 0, q.num.natAbs, q.den]

/-- Canonical graph-and-weight packet, without the accuracy parameter. -/
noncomputable abbrev encodeInstance {n : ℕ} (G : SimpleGraph (Fin n))
    (w : Fin n → ℚ) : List ℕ :=
  [n] ++ (List.ofFn fun u => List.ofFn fun v =>
    if G.Adj u v then 1 else 0).flatten ++
    (List.ofFn w).flatMap encodeRational

/-- Equal-length blocks can be separated without interpreting their contents. -/
private theorem blocks_injective {α β : Type*} (f : α → List β) (k : ℕ)
    (length : ∀ a, (f a).length = k) (injective : Function.Injective f) :
    ∀ xs ys : List α, xs.length = ys.length → xs.flatMap f = ys.flatMap f → xs = ys
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => nomatch h
  | _ :: _, [], h, _ => nomatch h
  | x :: xs, y :: ys, hlength, h =>
      let fields := List.append_inj h ((length x).trans (length y).symm)
      congrArg₂ List.cons (injective fields.1)
        (blocks_injective f k length injective xs ys (Nat.succ.inj hlength) fields.2)

private theorem blocks_length {α β : Type*} (f : α → List β) (k : ℕ)
    (length : ∀ a, (f a).length = k) (xs : List α) :
    (xs.flatMap f).length = xs.length * k :=
  calc
    (xs.flatMap f).length = (xs.map fun a => (f a).length).sum := List.length_flatMap
    _ = (xs.map fun _ => k).sum := congrArg (fun g => (xs.map g).sum) (funext length)
    _ = (List.replicate xs.length k).sum := congrArg List.sum List.map_const
    _ = xs.length * k := List.sum_replicate _ _

private theorem flag_injective (p q : Prop) [Decidable p] [Decidable q]
    (h : (if p then 1 else 0 : ℕ) = if q then 1 else 0) : p ↔ q :=
  ⟨fun hp => not_not.mp (fun hq => Nat.one_ne_zero
      ((if_pos hp).symm.trans (h.trans (if_neg hq)))),
   fun hq => not_not.mp (fun hp => Nat.one_ne_zero
      ((if_pos hq).symm.trans (h.symm.trans (if_neg hp))))⟩

private theorem signed_integer_injective : ∀ a b : ℤ,
    (if a < 0 then 1 else 0 : ℕ) = (if b < 0 then 1 else 0) →
    a.natAbs = b.natAbs → a = b
  | .ofNat _, .ofNat _, _, habs => congrArg Int.ofNat habs
  | .negSucc _, .negSucc _, _, habs => congrArg Int.negSucc (Nat.succ.inj habs)
  | .ofNat a, .negSucc b, hsign, _ => False.elim (Nat.zero_ne_one
      ((if_neg (not_lt.mpr (Int.natCast_nonneg a))).symm.trans
        (hsign.trans (if_pos (Int.negSucc_lt_zero b)))))
  | .negSucc a, .ofNat b, hsign, _ => False.elim (Nat.one_ne_zero
      ((if_pos (Int.negSucc_lt_zero a)).symm.trans
        (hsign.trans (if_neg (not_lt.mpr (Int.natCast_nonneg b))))))

private theorem rational_injective : Function.Injective encodeRational :=
  fun a b h =>
    let fields := List.cons.inj h
    let rest := List.cons.inj fields.2
    Rat.ext (signed_integer_injective a.num b.num fields.1 rest.1)
      (List.cons.inj rest.2).1

private theorem matrix_blocks {n : ℕ} (G : SimpleGraph (Fin n)) :
    (List.ofFn fun u => List.ofFn fun v => if G.Adj u v then 1 else 0).flatten =
      (List.ofFn fun u v => if G.Adj u v then 1 else 0).flatMap List.ofFn :=
  (congrArg List.flatten (List.map_ofFn (f := fun (u v : Fin n) => (if G.Adj u v then 1 else 0 : ℕ))
    (g := fun f : Fin n → ℕ => List.ofFn f))).symm

private theorem matrix_length {n : ℕ} (G : SimpleGraph (Fin n)) :
    (List.ofFn fun u => List.ofFn fun v => if G.Adj u v then 1 else 0).flatten.length = n*n :=
  (congrArg List.length (matrix_blocks G)).trans
    ((blocks_length List.ofFn n (fun _ => List.length_ofFn) _).trans
      (congrArg (· * n) List.length_ofFn))

private theorem matrix_injective {n : ℕ} (G H : SimpleGraph (Fin n))
    (h : (List.ofFn fun u => List.ofFn fun v => if G.Adj u v then 1 else 0).flatten =
      (List.ofFn fun u => List.ofFn fun v => if H.Adj u v then 1 else 0).flatten) : G = H :=
  let rows := blocks_injective List.ofFn n (fun _ => List.length_ofFn)
    List.ofFn_injective _ _ (List.length_ofFn.trans List.length_ofFn.symm)
    ((matrix_blocks G).symm.trans (h.trans (matrix_blocks H)))
  SimpleGraph.ext (funext fun u => funext fun v => propext
    (flag_injective _ _ (congrFun (congrFun (List.ofFn_injective rows) u) v)))

private theorem weights_injective {n : ℕ} (w z : Fin n → ℚ)
    (h : (List.ofFn w).flatMap encodeRational = (List.ofFn z).flatMap encodeRational) : w = z :=
  List.ofFn_injective (blocks_injective encodeRational 3 (fun _ => rfl)
    rational_injective _ _ (List.length_ofFn.trans List.length_ofFn.symm) h)

/-- The canonical packet determines all three mathematical instance fields. -/
private theorem encodeInstance_injective : Function.Injective
    (fun x : Instance => encodeInstance x.graph x.weights) :=
  fun x y h =>
    let order : x.order = y.order := (List.cons.inj h).1
    match x, y, order, h with
    | ⟨n,G,w⟩, ⟨_,H,z⟩, rfl, h =>
      let fields := List.append_inj (List.cons.inj h).2
        ((matrix_length G).trans (matrix_length H).symm)
      congrArg₂ (Instance.mk n) (matrix_injective G H fields.1) (weights_injective w z fields.2)

private theorem list_injective :
    ∀ xs ys : List ℕ, listToRaw nat xs = listToRaw nat ys → xs = ys
  | [], [], _ => rfl
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h
  | _ :: xs, _ :: ys, h =>
      let fields := Lax560851.StructuralPresentation.Raw.pair.inj h
      congrArg₂ List.cons (Lax560851.StructuralPresentation.Raw.nat.inj fields.1)
        (list_injective xs ys fields.2)

/-- The standard structural-list representation of a weighted graph. -/
noncomputable def input : Presentation Instance :=
  presentationOf (fun x => listToRaw nat (encodeInstance x.graph x.weights))

/-- Distinct mathematical instances have distinct structural representations. -/
theorem input_faithful : input.Faithful :=
  fun _ _ h => encodeInstance_injective (list_injective _ _ h)

end Lax263307.IndependentSetEncoding
end
