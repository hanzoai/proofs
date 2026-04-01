import Lake
open Lake DSL

package hanzoFormal where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

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

lean_lib Gateway where
  srcDir := "."
  roots := #[
    `Gateway.Auth,
    `Gateway.RateLimit
  ]

lean_lib Platform where
  srcDir := "."
  roots := #[
    `Platform.Deploy,
    `Platform.SBOM,
    `Platform.Monitoring
  ]

lean_lib KMS where
  srcDir := "."
  roots := #[
    `KMS.Secrets
  ]

lean_lib Compute where
  srcDir := "."
  roots := #[
    `Compute.PoAI,
    `Compute.ConfidentialCompute,
    `Compute.Swarm,
    `Compute.Billing
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.14.0"
