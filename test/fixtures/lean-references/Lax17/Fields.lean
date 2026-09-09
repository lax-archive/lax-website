/-! Navigation fixture, compiled with Lean 4.30.0 and no Mathlib. -/
namespace Lax17.Fields

/-- A packet's documented declaration. -/
structure Packet where
  /-- Its stored value. -/
  value : Nat
  /-- Its enabled flag. -/
  enabled : Bool

structure Other where
  value : Nat

def packet : Packet := { value := 3, enabled := true }
def updated (p : Packet) : Packet := { p with value := 4 }
def read (p : Packet) := p.value
def readOther (p : Other) := p.value
def constructor := Packet.mk 1 true

open Packet in
def viaOpen (p : Packet) := value p

export Packet (enabled)
def viaAlias (p : Packet) := enabled p

private def secret := 42
def viaPrivate := secret
def value := 7
def shadow (value : Nat) := value
def global := value
def unicode (𝒜 : Packet) := 𝒜.value
def «<script>» := 0
def escaped := «<script>»

inductive Choice where
  | first
  | second
def choice : Choice := .first

end Lax17.Fields
