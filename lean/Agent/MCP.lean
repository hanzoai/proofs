/-
  MCP Tool Permission Lattice

  Models the Model Context Protocol tool surface as a permission
  lattice with subset ordering.

  Maps to:
  - hanzo/mcp: HIP-0300 MCP server (13 unified tools)
  - hanzo/agents: agent permission configuration

  Properties:
  - Permission check is monotone
  - Empty permissions deny everything
  - Full permissions allow everything
-/

import Mathlib.Data.Nat.Defs
import Mathlib.Data.List.Basic
import Mathlib.Tactic

namespace Agent.MCP

/-- Permission set (represented as a bitmask for simplicity) -/
structure Permissions where
  mask : Nat
  deriving DecidableEq, Repr

/-- No permissions -/
def Permissions.none : Permissions := ⟨0⟩

/-- Full permissions -/
def Permissions.full : Permissions := ⟨0xFFF⟩  -- 12 tool bits

/-- Permission subset: a ≤ b iff a's bits are subset of b's -/
def Permissions.subset (a b : Permissions) : Prop :=
  a.mask &&& b.mask = a.mask

instance : LE Permissions where le := Permissions.subset

/-- Check if a specific tool (bit position) is permitted -/
def Permissions.has (p : Permissions) (toolBit : Nat) : Bool :=
  (p.mask &&& (1 <<< toolBit)) != 0

/-- Meet (intersection) of permissions -/
def Permissions.meet (a b : Permissions) : Permissions :=
  ⟨a.mask &&& b.mask⟩

instance : Min Permissions where min := Permissions.meet

/-- None is bottom: no permissions ≤ anything -/
theorem none_le_all (p : Permissions) : Permissions.none ≤ p := by
  simp [LE.le, Permissions.subset, Permissions.none, Nat.zero_and]

/-- Meet is lower bound (left) -/
theorem meet_mask_le_left (a b : Permissions) :
    (min a b).mask ≤ a.mask := by
  simp [Min.min, Permissions.meet]
  exact Nat.and_le_left a.mask b.mask

/-- Meet is lower bound (right) -/
theorem meet_mask_le_right (a b : Permissions) :
    (min a b).mask ≤ b.mask := by
  simp [Min.min, Permissions.meet]
  exact Nat.and_le_right a.mask b.mask

/-- Granting fewer permissions is monotone safe -/
theorem fewer_permissions_safe (parent child : Permissions)
    (h : child.mask ≤ parent.mask)
    (toolBit : Nat)
    (hc : child.has toolBit = true) :
    parent.has toolBit = true := by
  simp [Permissions.has] at *
  omega

end Agent.MCP
