/-
  Agent Safety Properties

  An agent has capabilities (tool set), a coeffect budget, and a
  delegation flag. Safety means agents cannot invoke tools outside
  their declared tool set, cannot exceed their coeffect budget, and
  cannot delegate more authority than they themselves hold.

  Maps to:
  - hanzo/dev: agentic coding harness
  - hanzo/agents: 88 specialized agents
  - hanzo/mcp: MCP tool surface

  Properties:
  - Agents cannot exceed declared coeffect budget
  - Tool invocations must be within capability set
  - Delegated agents inherit narrowed authority
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Tactic

namespace Agent.Safety

/-- MCP tool identifiers. -/
inductive Tool where
  | fs | exec | code | git | fetch | workspace
  | think | memory | plan | tasks | mode | browser
  deriving DecidableEq, Repr, Fintype

/-- An agent's capabilities: the tools it may call, its coeffect budget,
    and whether it is allowed to delegate. -/
structure AgentCaps where
  tools        : Finset Tool
  maxCoeffects : Nat
  canDelegate  : Bool

/-- A tool invocation request: which tool and at what coeffect cost. -/
structure ToolRequest where
  tool         : Tool
  coeffectCost : Nat

/-- A request is permitted when the tool is in the capability set and
    the coeffect cost is within the agent's budget. -/
def isPermitted (caps : AgentCaps) (req : ToolRequest) : Prop :=
  req.tool ∈ caps.tools ∧ req.coeffectCost ≤ caps.maxCoeffects

/-- **Theorem:** a permitted request uses a tool from the capability set. -/
theorem permitted_tool_in_caps
    {caps : AgentCaps} {req : ToolRequest} (h : isPermitted caps req) :
    req.tool ∈ caps.tools := h.1

/-- **Theorem:** a permitted request respects the coeffect budget. -/
theorem permitted_within_budget
    {caps : AgentCaps} {req : ToolRequest} (h : isPermitted caps req) :
    req.coeffectCost ≤ caps.maxCoeffects := h.2

/-- Delegation: a parent grants a child a subset of its tools and a
    budget capped at the parent's own budget. No re-delegation by
    default — the child cannot itself delegate further. -/
def delegate (parent : AgentCaps) (childTools : Finset Tool)
    (childBudget : Nat) : AgentCaps :=
  { tools        := childTools ∩ parent.tools
    maxCoeffects := min childBudget parent.maxCoeffects
    canDelegate  := false }

/-- **Theorem (tool narrowing):** any tool the delegate may call is a
    tool the parent could also call. -/
theorem delegate_narrows_tools
    (parent : AgentCaps) (ct : Finset Tool) (cb : Nat) (t : Tool)
    (h : t ∈ (delegate parent ct cb).tools) : t ∈ parent.tools := by
  unfold delegate at h
  exact (Finset.mem_inter.mp h).2

/-- **Theorem (budget narrowing):** the delegate's budget is at most
    the parent's budget. -/
theorem delegate_narrows_budget
    (parent : AgentCaps) (ct : Finset Tool) (cb : Nat) :
    (delegate parent ct cb).maxCoeffects ≤ parent.maxCoeffects := by
  unfold delegate
  exact Nat.min_le_right cb parent.maxCoeffects

/-- **Theorem (no re-delegation):** delegates cannot themselves delegate. -/
theorem delegate_no_redelegate
    (parent : AgentCaps) (ct : Finset Tool) (cb : Nat) :
    (delegate parent ct cb).canDelegate = false := rfl

end Agent.Safety
