import Lake
open Lake DSL

package hanzoFormal where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

-- Every library is a default target, so `lake build` builds the whole corpus.
-- With the attribute on one library, `lake build` compiles that library's
-- import closure and reports success for everything else.

@[default_target]
lean_lib Agent where
  srcDir := "."
  roots := #[
    `Agent.Safety,
    `Agent.MCP,
    `Agent.Delegation,
    `Agent.Workflow,
    `Agent.Identity,
    `Agent.Memory
  ]

@[default_target]
lean_lib Gateway where
  srcDir := "."
  roots := #[
    `Gateway.Auth,
    `Gateway.RateLimit
  ]

@[default_target]
lean_lib Platform where
  srcDir := "."
  roots := #[
    `Platform.Deploy,
    `Platform.SBOM,
    `Platform.Monitoring
  ]

@[default_target]
lean_lib KMS where
  srcDir := "."
  roots := #[
    `KMS.Secrets
  ]

@[default_target]
lean_lib Compute where
  srcDir := "."
  roots := #[
    `Compute.PoAI,
    `Compute.ConfidentialCompute,
    `Compute.Swarm,
    `Compute.Billing
  ]

@[default_target]
lean_lib CRDT where
  srcDir := "."
  roots := #[
    `CRDT.Privacy,
    `CRDT.Commutativity,
    `CRDT.Anchor
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.14.0"
