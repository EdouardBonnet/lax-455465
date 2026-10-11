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
The finite event thresholds, product-volume doubling argument, and logarithmic
iteration budget are proved, including the bound that a failed grid cell
doubles the product volume along its actual rational candidate list. The
computable finite threshold search is proved to return a successful positive
radius within its prescribed budget, for either computed orientation.

Sorting arbitrary rational potentials now produces the actual finite layers
used by the sweep, preserving all potential differences. The region
selection compares the two residual ball masses and strictly decreases the
positive-weight support. Its non-seed volume is bounded by the decrease in
residual length cost, giving total boundary charge at most 2 beta W with
seed W/p and at most p removals. The large-ball branch constructs a rational
potential with separation at least 1/6 and returns a cut of ratio at most
6W by the actual finite sweep. For the ordered-region branch, every cut
between region positions is bounded by the sum of the chosen removal
boundaries, charging each crossing arc at its earliest removed endpoint.

The ordered-region threshold scan is also proved: with every block below
2M/3, it returns a cut of product demand at least 5M²/36. Reordering preserves
block masses, and a boundary charge at most 8KM²W gives cut ratio at most
(288/5)KW.

The ordinary algorithm still needs the complete region loop and its
partition invariants, followed by the RAM implementation and composition of
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

The registered LP development `lax-109476` supplies its public concepts and
proved exact solver. Both packages are pinned to
`https://github.com/EdouardBonnet/lax-109476`, commit
`0a042604c7ae1ef4cd9a4c7d82eb902f313d4864`, folders `concepts` and `proofs`.
The dependency uses the registered source in strict archive validation.

## Validation

```sh
lax build /home/ebonnet/Bitbucket/lax/leighton-rao --replay
```

Build artifacts use the existing shared mathlib and RAM dependencies.
