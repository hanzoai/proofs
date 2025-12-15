export type ProofTool = 'lean4' | 'coq'
export type ProofStatus = 'proved' | 'partial' | 'axiom'

export interface ProofConfig {
  id: string
  title: string
  subtitle: string
  abstract: string
  tool: ProofTool
  status: ProofStatus
  theoremCount: number
  sourceUrl: string
  githubUrl: string
  date: string
  authors: string[]
  tags: string[]
  relatedPapers?: string[]
}

export interface SiteConfig {
  name: string
  fullName: string
  description: string
  website: string
  github: string
  primaryColor: string
  secondaryColor: string
  accentColor: string
  logo: string
  proofs: ProofConfig[]
}

export const siteConfig: SiteConfig = {
  name: 'Hanzo AI',
  fullName: 'Hanzo AI Research Team',
  description: 'Machine-checked proofs for AI agent systems, ML frameworks, and distributed compute infrastructure.',
  website: 'https://hanzo.ai',
  github: 'https://github.com/hanzoai',
  primaryColor: '#3498DB',
  secondaryColor: '#2980B9',
  accentColor: '#E67E22',
  logo: '/logos/hanzo-logo.svg',
  proofs: [
    {
      id: 'agent-grpo',
      title: 'Agent GRPO Training',
      subtitle: 'Convergence Proofs for Group Relative Policy Optimization',
      abstract: 'Formal proof that Group Relative Policy Optimization converges to a stable policy under bounded reward variance. Establishes monotonic improvement guarantees and KL-divergence bounds for multi-agent training.',
      tool: 'lean4',
      status: 'proved',
      theoremCount: 4,
      sourceUrl: 'https://github.com/hanzoai/proofs/blob/main/lean/Agent/GRPO.lean',
      githubUrl: 'https://github.com/hanzoai/proofs',
      date: '2026-03-01',
      authors: ['Zach Kelling', 'Hanzo AI Research'],
      tags: ['GRPO', 'Convergence', 'Policy Optimization', 'RL'],
      relatedPapers: ['GRPO Training Framework'],
    },
    {
      id: 'federated-consensus',
      title: 'Federated Agent Consensus',
      subtitle: 'Byzantine Fault Tolerance in Multi-Agent Systems',
      abstract: 'Proof of Byzantine fault tolerance for federated agent coordination. Establishes safety under f < n/3 malicious agents and liveness under partial synchrony for distributed decision-making.',
      tool: 'lean4',
      status: 'proved',
      theoremCount: 3,
      sourceUrl: 'https://github.com/hanzoai/proofs/blob/main/lean/Agent/Consensus.lean',
      githubUrl: 'https://github.com/hanzoai/proofs',
      date: '2026-02-15',
      authors: ['Zach Kelling', 'Hanzo AI Research'],
      tags: ['BFT', 'Multi-Agent', 'Consensus', 'Federated'],
      relatedPapers: ['Federated Agent Architecture'],
    },
    {
      id: 'jin-architecture',
      title: 'Jin Architecture Verification',
      subtitle: 'Multimodal Pipeline Correctness',
      abstract: 'Formal verification of the Jin multimodal architecture proving type safety across vision-language-audio pipelines. Establishes that cross-modal attention preserves embedding dimensionality and semantic alignment.',
      tool: 'coq',
      status: 'proved',
      theoremCount: 5,
      sourceUrl: 'https://github.com/hanzoai/proofs/blob/main/coq/Jin/Pipeline.v',
      githubUrl: 'https://github.com/hanzoai/proofs',
      date: '2026-01-20',
      authors: ['Zach Kelling', 'Hanzo AI Research'],
      tags: ['Multimodal', 'Type Safety', 'Pipeline', 'Jin'],
      relatedPapers: ['Jin Unified Multimodal Framework'],
    },
    {
      id: 'mcp-safety',
      title: 'MCP Protocol Safety',
      subtitle: 'Model Context Protocol Message Ordering',
      abstract: 'Proof that Model Context Protocol maintains causal message ordering under concurrent tool invocations. Establishes exactly-once delivery semantics and context window consistency for agent-model communication.',
      tool: 'lean4',
      status: 'proved',
      theoremCount: 3,
      sourceUrl: 'https://github.com/hanzoai/proofs/blob/main/lean/MCP/Safety.lean',
      githubUrl: 'https://github.com/hanzoai/proofs',
      date: '2026-02-01',
      authors: ['Zach Kelling', 'Hanzo AI Research'],
      tags: ['MCP', 'Message Ordering', 'Causal', 'Protocol'],
      relatedPapers: ['Model Context Protocol Specification'],
    },
    {
      id: 'candle-ml',
      title: 'Candle ML Framework',
      subtitle: 'Tensor Operation Correctness & Gradient Flow',
      abstract: 'Formal verification of tensor operation correctness in the Candle ML framework. Proves shape preservation across broadcast operations, gradient flow through computational graphs, and numerical stability of softmax.',
      tool: 'coq',
      status: 'partial',
      theoremCount: 4,
      sourceUrl: 'https://github.com/hanzoai/proofs/blob/main/coq/Candle/Tensor.v',
      githubUrl: 'https://github.com/hanzoai/proofs',
      date: '2026-03-10',
      authors: ['Zach Kelling', 'Hanzo AI Research'],
      tags: ['Tensor', 'Gradient', 'ML Framework', 'Numerical'],
    },
    {
      id: 'llm-gateway',
      title: 'LLM Gateway Routing',
      subtitle: 'Request Routing Invariants',
      abstract: 'Proof of correctness for the LLM gateway routing layer. Establishes that weighted load balancing preserves fairness, rate limiting prevents starvation, and fallback routing guarantees availability under partial provider failure.',
      tool: 'lean4',
      status: 'proved',
      theoremCount: 3,
      sourceUrl: 'https://github.com/hanzoai/proofs/blob/main/lean/Gateway/Routing.lean',
      githubUrl: 'https://github.com/hanzoai/proofs',
      date: '2026-01-15',
      authors: ['Zach Kelling', 'Hanzo AI Research'],
      tags: ['Gateway', 'Load Balancing', 'Routing', 'Availability'],
    },
    {
      id: 'self-improving',
      title: 'Self-Improving Agents',
      subtitle: 'Convergence Bounds for Recursive Self-Improvement',
      abstract: 'Establishes convergence bounds for agents that recursively improve their own policy. Proves that improvement magnitude is monotonically decreasing and bounded, preventing divergence under the capability amplification loop.',
      tool: 'lean4',
      status: 'partial',
      theoremCount: 2,
      sourceUrl: 'https://github.com/hanzoai/proofs/blob/main/lean/Agent/SelfImprovement.lean',
      githubUrl: 'https://github.com/hanzoai/proofs',
      date: '2026-03-20',
      authors: ['Zach Kelling', 'Hanzo AI Research'],
      tags: ['Self-Improvement', 'Convergence', 'Safety', 'Recursive'],
      relatedPapers: ['Agent Self-Improvement Bounds'],
    },
    {
      id: 'unified-harness',
      title: 'Unified Harness',
      subtitle: 'Test Harness Completeness',
      abstract: 'Formal proof of test harness completeness for the Hanzo agent evaluation framework. Establishes that the harness covers all reachable agent states and that no observable behavior escapes the test oracle.',
      tool: 'coq',
      status: 'proved',
      theoremCount: 3,
      sourceUrl: 'https://github.com/hanzoai/proofs/blob/main/coq/Harness/Completeness.v',
      githubUrl: 'https://github.com/hanzoai/proofs',
      date: '2026-02-28',
      authors: ['Zach Kelling', 'Hanzo AI Research'],
      tags: ['Testing', 'Completeness', 'Harness', 'Evaluation'],
    },
  ],
}
