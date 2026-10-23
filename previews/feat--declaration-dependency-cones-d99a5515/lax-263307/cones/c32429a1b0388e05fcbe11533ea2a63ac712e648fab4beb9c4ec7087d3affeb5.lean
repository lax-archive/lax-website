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
namespace Lax263307
end Lax263307

namespace Lax263307.WeightedIndependentSet
end Lax263307.WeightedIndependentSet

namespace Lax263307.WeightedIndependentSet.Instance
end Lax263307.WeightedIndependentSet.Instance
end

-- Lax560851.StructuralPresentation
section
namespace Lax560851
end Lax560851

namespace Lax560851.StructuralPresentation
end Lax560851.StructuralPresentation

namespace Lax560851.StructuralPresentation.Presentation
end Lax560851.StructuralPresentation.Presentation

namespace Lax560851.StructuralPresentation.Raw
end Lax560851.StructuralPresentation.Raw

namespace Lax560851.StructuralPresentation.Raw.nat
end Lax560851.StructuralPresentation.Raw.nat

namespace Lax560851.StructuralPresentation.Raw.nodes
end Lax560851.StructuralPresentation.Raw.nodes

namespace Lax560851.StructuralPresentation.Raw.pair
end Lax560851.StructuralPresentation.Raw.pair
end

-- Lax560851.StructuralCombinators
section
namespace Lax560851.StructuralCombinators
end Lax560851.StructuralCombinators

namespace Lax560851.StructuralCombinators.Derivable
end Lax560851.StructuralCombinators.Derivable

namespace Lax560851.StructuralCombinators.Generated
end Lax560851.StructuralCombinators.Generated

namespace Lax560851.StructuralCombinators.Lawful
end Lax560851.StructuralCombinators.Lawful

namespace Lax560851.StructuralCombinators.Raw
end Lax560851.StructuralCombinators.Raw

namespace Lax560851.StructuralCombinators.SizeLaws
end Lax560851.StructuralCombinators.SizeLaws

namespace Lax560851.StructuralCombinators.listFromRaw
end Lax560851.StructuralCombinators.listFromRaw

namespace Lax560851.StructuralCombinators.listToRaw
end Lax560851.StructuralCombinators.listToRaw

namespace Lax560851.StructuralCombinators.nat
end Lax560851.StructuralCombinators.nat

namespace Lax560851.StructuralCombinators.prod
end Lax560851.StructuralCombinators.prod

namespace Lax560851.StructuralCombinators.Raw.constructorCharsCode
end Lax560851.StructuralCombinators.Raw.constructorCharsCode

namespace Lax560851.StructuralCombinators.Raw.fields
end Lax560851.StructuralCombinators.Raw.fields
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

private theorem weights_injective {n : ℕ} (w z : Fin n → ℚ)
    (h : (List.ofFn w).flatMap encodeRational = (List.ofFn z).flatMap encodeRational) : w = z :=
  List.ofFn_injective (blocks_injective encodeRational 3 (fun _ => rfl)
    rational_injective _ _ (List.length_ofFn.trans List.length_ofFn.symm) h)

end Lax263307.IndependentSetEncoding
end
