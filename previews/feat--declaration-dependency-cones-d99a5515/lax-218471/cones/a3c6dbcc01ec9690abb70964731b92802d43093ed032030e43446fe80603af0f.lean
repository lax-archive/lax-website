-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum

-- Lax218471.PolynomialTime
section
namespace Lax218471
end Lax218471

namespace Lax218471.PolynomialTime
end Lax218471.PolynomialTime

namespace Lax218471.PolynomialTime.Implementation
end Lax218471.PolynomialTime.Implementation
end

-- Lax218471.Subroutine
section
namespace Lax218471
end Lax218471

namespace Lax218471.Subroutine
end Lax218471.Subroutine

namespace Lax218471.Subroutine.Routine
end Lax218471.Subroutine.Routine

namespace Lax218471.Subroutine.Store
end Lax218471.Subroutine.Store

namespace Lax218471.Subroutine.Routine.boundary
end Lax218471.Subroutine.Routine.boundary
end

-- Lax218471.Programs
section
namespace Lax218471.Programs.Executes
end Lax218471.Programs.Executes

namespace Lax218471.Programs.Op.apply
end Lax218471.Programs.Op.apply

namespace Lax218471.Programs

open Subroutine

variable {K A σ I : Type}

/-- One local operation; the control type is finite when programs are compiled. -/
inductive Op (K A σ : Type)
  | push (k : K) (f : σ → A)
  | pop (k : K) (f : σ → Option A → σ)
  | peek (k : K) (f : σ → Option A → σ)
  | load (f : σ → σ)

/-- A finite program with named library calls. Loops retain their body as finite code. -/
inductive Program (K A σ I : Type)
  | atom (o : Op K A σ)
  | call (i : I) (port : K)
  | seq (p q : Program K A σ I)
  | branch (b : σ → Bool) (p q : Program K A σ I)
  | loop (b : σ → Bool) (p : Program K A σ I)

end Lax218471.Programs
end
