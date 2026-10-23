-- Lax dependency cone
-- Lean: v4.30.0
-- Mathlib: c5ea00351c28e24afc9f0f84379aa41082b1188f

import Mathlib.ModelTheory.Semantics

-- Lax52.MSOSyntax
section
namespace Lax52
end Lax52

namespace Lax52.MSOSyntax
end Lax52.MSOSyntax

namespace Lax52.MSOSyntax.Formula
end Lax52.MSOSyntax.Formula

namespace Lax52.MSOSyntax.Formula.equal
end Lax52.MSOSyntax.Formula.equal

namespace Lax52.MSOSyntax.Formula.exFO
end Lax52.MSOSyntax.Formula.exFO

namespace Lax52.MSOSyntax.Formula.exSO
end Lax52.MSOSyntax.Formula.exSO

namespace Lax52.MSOSyntax.Formula.falsum
end Lax52.MSOSyntax.Formula.falsum

namespace Lax52.MSOSyntax.Formula.mem
end Lax52.MSOSyntax.Formula.mem

namespace Lax52.MSOSyntax.Formula.neg
end Lax52.MSOSyntax.Formula.neg

namespace Lax52.MSOSyntax.Formula.or
end Lax52.MSOSyntax.Formula.or

namespace Lax52.MSOSyntax.Formula.rel
end Lax52.MSOSyntax.Formula.rel
end

-- Lax52.MSOSemantics
section
namespace Lax52.MSOSemantics.Realize
end Lax52.MSOSemantics.Realize

namespace Lax52.MSOSemantics

open FirstOrder

open FirstOrder.Language

open FirstOrder.Language.Structure

open Lax52.MSOSyntax

universe u v w

variable {L : Language.{u, v}} {M : Type w} [L.Structure M]

/-- Extend a valuation by putting a newly bound variable at index zero. -/
def consVal {n : Nat} (x : M) (v : Fin n → M) : Fin (n + 1) → M :=
  Fin.cases x v

end Lax52.MSOSemantics
end
