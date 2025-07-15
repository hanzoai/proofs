/-
  Agent Safety Properties

  An agent has capabilities (tool list), a trust level,
  and a coeffect budget. Safety means agents cannot exceed
  their declared boundaries.

  Maps to:
  - hanzo/dev: agentic coding harness
  - hanzo/agents: 88 specialized agents
  - hanzo/mcp: MCP tool surface

  Properties:
  - Agents cannot exceed declared coeffect budget
  - Tool invocations must be within capability set
  - Delegated agents inherit narrowed authority
-/

import Mathlib.Data.Nat.Defs
import Mathlib.Data.List.Basic
import Mathlib.Tactic

namespace Agent.Safety

/-- MCP tool identifiers -/
inductive Tool where
  | fs | exec | code | git | fetch | workspace
  | think | memory | plan | tasks | mode | browser
  deriving DecidableEq, Repr

/-- Agent capability set -/
structure AgentCaps where
  tools : List Tool
  maxCoeffects : Nat    -- coeffect budget
  canDelegate : Bool    -- can spawn sub-agents
  deriving DecidableEq, Repr

/-- Tool invocation request -/
structure ToolRequest where
  tool : Tool
  coeffectCost : Nat
  deriving Repr

/-- Check if a tool request is permitted -/
def isPermitted (caps : AgentCaps) (req : ToolRequest) : Bool :=
  caps.tools.contains req.tool && req.coeffectCost ≤ caps.maxCoeffects

/-- Permitted requests use tools from the capability set -/
theorem permitted_tool_in_caps (caps : AgentCaps) (req : ToolRequest)
    (h : isPermitted caps req = true) :
    caps.tools.contains req.tool = true := by
  simp [isPermitted, Bool.and_eq_true] at h
  exact h.1

/-- Permitted requests don't exceed coeffect budget -/
theorem permitted_within_budget (caps : AgentCaps) (req : ToolRequest)
    (h : isPermitted caps req = true) :
    req.coeffectCost ≤ caps.maxCoeffects := by
  simp [isPermitted, Bool.and_eq_true, Nat.ble_eq] at h
  exact h.2

/-- Delegated agent gets narrowed capabilities -/
def delegate (parent : AgentCaps) (childTools : List Tool) (childBudget : Nat) : AgentCaps :=
  { tools := childTools.filter (parent.tools.contains ·)
  , maxCoeffects := min childBudget parent.maxCoeffects
  , canDelegate := false }  -- no re-delegation by default

/-- Delegated tools are subset of parent -/
theorem delegate_narrows_tools (parent : AgentCaps) (ct : List Tool) (cb : Nat) (t : Tool)
    (h : (delegate parent ct cb).tools.contains t = true) :
    parent.tools.contains t = true := by
  simp [delegate, List.contains_eq_any_beq] at h
  simp [List.any_eq_true, List.mem_filter, List.contains_eq_any_beq] at h
  obtain ⟨x, ⟨_, hx_parent⟩, hxt⟩ := h
  simp [List.any_eq_true]
  exact ⟨x, hx_parent, hxt⟩

/-- Delegated budget doesn't exceed parent -/
theorem delegate_narrows_budget (parent : AgentCaps) (ct : List Tool) (cb : Nat) :
    (delegate parent ct cb).maxCoeffects ≤ parent.maxCoeffects := by
  simp [delegate]
  exact Nat.min_le_right cb parent.maxCoeffects

end Agent.Safety
