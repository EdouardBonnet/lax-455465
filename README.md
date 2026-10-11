# Deterministic Leighton–Rao flow–cut algorithms

Submission `lax-455465`, based on Tom Leighton and Satish Rao,
*Multicommodity Max-Flow Min-Cut Theorems and Their Use in Designing
Approximation Algorithms*, JACM 46(6), 787–832 (1999),
[doi:10.1145/331524.331526](https://doi.org/10.1145/331524.331526).

The reference PDF is `leighton-rao.pdf`, ignored by git.

## Scope

The common algorithm handles rational product demands in directed and
undirected networks. It returns a joint certificate consisting of a
positive-demand cut and a feasible rational concurrent arc flow, with cut ratio
at most a universal constant times log₂(p) times the returned flow value.
Here p counts the positive-weight vertices. Four variants specialize this
single algorithm and retain its program and exact output guarantees.

The uniform short-path construction of Theorem 18 remains a separate
algorithmic statement: its additional path-length bound does not follow
from the ordinary flow–cut guarantee. Matching lower-bound examples,
nonalgorithmic statements for arbitrary real inputs, and applications to
other approximation problems are outside this submission.

## Proof status

| Statement | Status | Public proof dependency |
| --- | --- | --- |
| `RamProductFlowCut` | Open | — |
| `RamDirectedSparsestCut` | Conditional proof | `RamProductFlowCut` |
| `RamUndirectedSparsestCut` | Conditional proof | `RamProductFlowCut` |
| `RamDirectedUniformFlowCut` | Conditional proof | `RamDirectedSparsestCut` |
| `RamUniformFlowCut` | Conditional proof | `RamUndirectedSparsestCut` |
| `RamUniformShortPathFlow` | Open | — |

These are six algorithmic statements and five definition concepts. The
conditional proofs preserve one program, one universal approximation
constant, and the same joint output. The core algorithm and short-path
algorithm are not yet discharged from background axioms. No `sorry` or
`admit` is used. Lax concept axioms represent the open statements.

The proof package's directed-flow LP uses n⁴+1 nonnegative variables and
n²+2n³ inequalities. Its capacity and conservation constraints encode arc
flows, without enumerating simple paths. Supporting proofs are internal
lemmas, rather than independent public side observations. They prove exact
LP equivalence, feasibility and boundedness, extraction of a rational flow
and matching dual from the actual LP solver, dual lengths and potentials,
and the directed-to-undirected conversion. The rational threshold-selection
routine and its finite layer-cake rounding bound are also proved. Exact
rational min-plus distances preserve the dual separation and cost bounds.
Finite region-volume growth bounds are proved between vertex-distance events.

The ordinary algorithm still needs the region-growing construction with
its logarithmic guarantee and the RAM implementation and composition of
the reduction and rounding stages. The short-path construction is open.

## Conventions and dependencies

Undirected capacities are symmetric and shared between both directions.
Each ordered pair has half its unordered product demand. Directed arcs
have separate capacities and full product demand for each ordered pair.
Both models use cuts of positive demand only, require p ≥ 2, and allow
zero-weight transit vertices. Uniform inputs have all weights equal to one.

The registered `Lax759944.RamPolytime.RamPolytime` predicate is pinned to
`https://github.com/szymtor/RAM-TM`, commit
`134e398cef46599371df99f10c9007bc34ba3868`, folder `concepts`. Its word RAM
is `Lax808846`, pinned transitively to
`https://github.com/lax-archive/lax-submissions`, commit
`9394e531cc51cb67a0214bca3f9264dfe97ba5c7`, folder `word-ram/concepts`.

The LP development `lax-109476` is reused as a local sibling while it is
still a draft. It must be registered and the sibling requires replaced
with its immutable git pins before strict archive submission. Local
iteration therefore uses `lax build --nonstrict`; strict builds must not
silently accept this draft dependency.

## Validation

```sh
lax build /home/ebonnet/Bitbucket/lax/leighton-rao --nonstrict --replay
```

Build artifacts use the existing shared mathlib and RAM dependencies.
