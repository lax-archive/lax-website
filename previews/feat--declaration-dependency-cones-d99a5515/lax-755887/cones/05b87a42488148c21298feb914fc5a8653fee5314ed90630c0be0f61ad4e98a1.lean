-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib

-- Lax755887.ReusedKey
section
namespace Lax755887.ReusedKey

def probability (event : Bool → Bool) : ℚ :=
  ((if event false then 1 else 0) + (if event true then 1 else 0)) / 2

def SameLaw {α : Type} (X Y : Bool → α) : Prop :=
  ∀ test : α → Bool, probability (fun k => test (X k)) = probability (fun k => test (Y k))

end Lax755887.ReusedKey
end

-- Lax755887.ReusedKeyContract
section
namespace Lax755887.ReusedKeyContract

open Lax755887.ReusedKey

axiom parallel_composition {α β : Type} (X X' : Bool → α) (Y Y' : Bool → β) :
  SameLaw X X' → SameLaw Y Y' →
    SameLaw (fun k => (X k, Y k)) (fun k => (X' k, Y' k))

end Lax755887.ReusedKeyContract
end
