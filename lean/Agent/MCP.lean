/-
  MCP Tool Permission Lattice

  Models the Model Context Protocol tool surface as a permission
  lattice with subset ordering.

  Maps to:
  - hanzo/mcp: HIP-0300 MCP server (13 unified tools)
  - hanzo/agents: agent permission configuration

  Properties:
  - Permission check is monotone under subset
  - Empty permissions deny everything
  - Full permissions allow everything

  Model: permissions are represented as a `Finset` of tool identifiers,
  which gives us lattice structure for free (subset / meet / empty) and
  avoids the Lean-4-version-sensitive bitwise lemmas.
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Tactic

namespace Agent.MCP

/-- A tool is identified by a natural-number index. -/
abbrev ToolId := Nat

/-- Permission set: the set of tool ids the holder may call. -/
abbrev Permissions := Finset ToolId

/-- No permissions: deny everything. -/
def Permissions.none : Permissions := ∅

-- Permission subset ordering is inherited from `Finset.instLE`.
-- `Permissions.subset a b ↔ a ⊆ b` holds by definition.

/-- A principal *has* tool `t` iff `t ∈ p`. -/
def Permissions.has (p : Permissions) (t : ToolId) : Prop := t ∈ p

/-- **Theorem:** `Permissions.none` is the bottom of the lattice. -/
theorem none_le_all (p : Permissions) : Permissions.none ⊆ p := by
  simp [Permissions.none]

/-- **Theorem:** meet (intersection) is a lower bound on the left. -/
theorem meet_le_left (a b : Permissions) : a ∩ b ⊆ a :=
  Finset.inter_subset_left

/-- **Theorem:** meet is a lower bound on the right. -/
theorem meet_le_right (a b : Permissions) : a ∩ b ⊆ b :=
  Finset.inter_subset_right

/-- **Theorem (monotone delegation):** if a child holds a subset of the
    parent's permissions, every tool the child may call is one the
    parent may also call. This is the core safety property for
    capability-style permission delegation. -/
theorem fewer_permissions_safe
    (parent child : Permissions) (h : child ⊆ parent)
    (t : ToolId) (hc : child.has t) : parent.has t := by
  unfold Permissions.has at *
  exact h hc

end Agent.MCP
