-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib

-- Lax755887.Stuttering
section
namespace Lax755887
end Lax755887

namespace Lax755887.Stuttering
end Lax755887.Stuttering
end

-- Lax755887.StutteringContract
section
namespace Lax755887.StutteringContract

open Lax755887.Stuttering

axiom termination_transfer {A B : Type} (concrete : A → A → Prop)
    (abstract : B → B → Prop) (view : A → B) (terminates : WellFounded abstract)
    (simulation : ∀ s t, concrete t s → view t = view s ∨ abstract (view t) (view s)) :
    WellFounded concrete

end Lax755887.StutteringContract
end
