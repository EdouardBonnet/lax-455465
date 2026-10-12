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

The complete deterministic region loop and its history invariants are now
proved. Within the initial support budget it either finds two large root
balls or exhausts all positive-weight vertices through small removals.
Earliest-removal labels preserve the actual block masses and identify each
label charge with its residual boundary. The complete history telescopes to
the required boundary bound. The zero-cost branch scans a positively
separated pair and returns a zero-capacity cut without a positive seed.

The finite rational rounding algorithm and its logarithmic approximation
bound are proved for all nonnegative separated directed metrics. Applied to
the exact flow-LP dual distances, it yields a joint cut and concurrent-flow
certificate with universal constant 512. The actual certificate
postprocessing function is proved correct for every valid output of the LP
solver, in both directed and symmetric undirected inputs.

The registered LP solver now supplies a fixed virtual RAM program with
polynomial execution and word-width bounds through its public theorem.
Sparse virtual memory exactly simulates every registered RAM instruction,
starts from zero memory, and stores at most one write per successful step.
Native host lookup and append commands preserve the sparse representation,
with lookup cost linear in the number of writes and append cost constant.
The virtual arithmetic commands prove the exact wraparound, complement,
and guarded-shift behavior at a word width independent of the host width.
Canonical rational vector and matrix parsers preserve their unconsumed tail.
The instance parser recovers the public flow encoding exactly, and the LP
certificate parser recovers all three encoded LP outcomes. The complete
word transformation, parameterized by the registered LP solver, emits the
same valid joint certificate supplied by the mathematical rounding proof.

The complete native interpreter is proved for all eighteen instructions,
including indirect memory, both input views, buffered output, exhausted reads,
and halting. It starts with zero virtual memory and follows the source
program's actual running flag. A source execution of k steps uses buffers
of k+1 entries and at most (k+1)(4|p|+32k+104)+18 native instructions,
where p is the fixed source program. Its virtual word width is independent
of the host width. The physical input copy is also proved for arbitrary
logical words. The registered LP concept theorem now supplies a native
invocation producing exactly the same valid certificate in a private buffer,
with explicit sufficient host bounds and quadratic simulation overhead.
The full invocation computes the virtual word width from the actual LP
buffer using its binary-size counter and a fixed Horner program, frames the
input, and runs the interpreter. It requires no supplied word-width value.

The runtime binary-size counter and fixed Horner polynomial programs are
proved. The dense flow-LP input has binary size at most 128(L+1)^8, where L
is the original input size; this includes all dimensions and coefficients.
Unsigned rational input pairs and canonical signed LP rational buffer output
are implemented with exact execution proofs. A sufficient host width is
linear in the virtual width, source time, input length, and fixed program
allowance, and works at every larger host width.

The flat numerical flow-LP encoding is proved equal to the public LP input
encoding, including zero dimensions. Fixed native commands compute its
dimensions, row and column indices, and every matrix coefficient. The
coefficient execution proof includes all conservation signs, equal endpoints,
self-loops, and exact normalized products of two input weights.

The complete native LP builder emits the header, matrix, bounds, and
objective in the registered encoding. Its instruction cost is at most
10000(L+1)^8 for canonical flow inputs, counting rational normalization and
output. A single fixed native program composes this construction with the
registered LP invocation and produces a valid certificate for that exact LP.

The flow-LP component now has one fixed native command and fixed polynomial
time and word bounds, with correctness at every larger host word width.
The native input decoder reads the edge model and graph order from the copied
input, computes all dimensions, and normalizes the weights and capacities
into the exact initialized buffers required by construction.

The LP stage now composes physical input reading, graph decoding, LP
construction, execution, and certificate decoding into one fixed native
command. For inputs with at least two positive weights it obtains the actual
matching primal and dual witnesses, in canonical unsigned rational buffers.
The interpreter preserves the source graph, dimensions, and edge model.

The native shortest-distance command now performs all runtime Floyd–Warshall
pivots and exactly matches the mathematical min-plus algorithm. A common
denominator invariant bounds every intermediate matrix and normalized
addition candidate. The actual returned LP certificate supplies the initial
coordinate bounds, giving polynomial distance bit heights in the original
graph input size.

The distance initializer reads the actual decoded dual coordinates and zeros
the diagonal. One fixed native command now composes physical graph input,
LP construction and execution, certificate decoding, and the full shortest-
distance computation, with polynomial time and word bounds in the source
input size. The original graph and matching flow buffers are preserved.

Native commands now extract both distance vectors for a runtime root,
perform clipped edge-volume arithmetic, and sum the exact metric cost from
the actual source capacities and computed distance buffer. Shared denominator
invariants give polynomial heights for all partial rational sums. A bounded
native scan is proved to record the first successful test. The radius search
scans grid endpoints and clipped vertex events directly; its correctness
proof retains the same volume-growth and approximation guarantees.

The physical-input pipeline also computes and saves the exact metric cost
with uniform polynomial resources. Native strict-ball masks and masked mass
sums are proved to match the region-selection expressions, including
threshold equality and zero-weight vertices. Coordinatewise products
implement residual mask intersection and weighting without changing source
buffers. Runtime endpoint masks and capacity sums now compute both boundary
orientations exactly, including threshold equality. A fixed command
initializes every vertex as active and reconstructs residual capacities and
weights from the original graph and current membership flags. These
reconstructed arrays match the residual graph in the region-loop proof, and
their coordinate heights stay bounded by those of the original input.
The native root scan matches the first positive residual weight. Complete
volume commands in both directions read and clip each edge contribution,
sum it, and add the seed; one polynomial bound covers all intermediates and
their execution resources. The computed ball masses also determine the
orientation, with outward ties matching the region-loop definition.
A single fixed native query now composes both ball masses, orientation
selection, the chosen boundary and volume, multiplication by the slope, and
the final positive-radius acceptance test. Its returned flag agrees exactly
with the mathematical candidate-search predicate, with a polynomial bound
covering every intermediate rational.

The complete native radius buffer is proved to match the unsorted grid and
clipped events used by the mathematical search. A bounded native scan
records its first accepted candidate, and a final query restores that
candidate’s exact masks, orientation, boundary, and volume. The recorded
choice is connected to the mathematical region-search function.

Native initialization now sums the original vertex weights and counts
their positive support from the canonical input buffer. Repeated integer
halving computes the finite logarithmic grid budget. Exact rational
operations then derive the seed, radius budget, slope, and grid step from
this support, total weight, and existing metric cost. Their execution and
intermediate coordinate-height bounds are proved.

The ordinary algorithm still needs malformed-input guards, the remaining
native region loop and cut rounding, their resource bounds, and final
composition. The separate short-path construction is open.

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

The registered LP development `lax-109476` supplies its public concepts,
including the exact polynomial-time solver theorem. Its concept package is pinned to
`https://github.com/EdouardBonnet/lax-109476`, commit
`0a042604c7ae1ef4cd9a4c7d82eb902f313d4864`, folder `concepts`.
LR uses this registered theorem directly, without importing the LP proof
package or replaying its implementation. The dependency uses the registered
source in strict archive validation.

The native implementation uses the verified `Lax808846Proofs` structured
RAM compiler and its execution/resource interface, pinned to the same
`9394e531cc51cb67a0214bca3f9264dfe97ba5c7` revision, folder `word-ram/proofs`.
This compiler is implementation infrastructure; the LP solver remains a
public concept dependency.

`RamArithmetic`, `RamRational`, `RamComparison`, and `RamTransfer` reuse
generic RAM utilities from the registered LP source at
`0a042604c7ae1ef4cd9a4c7d82eb902f313d4864`, under its Apache-2.0 license.
Their namespaces and local imports are adapted. Each file records the
source revision, and this repository retains the Apache-2.0 license.
The sparse virtual machine and host memory commands are new LR support
proofs.

## Validation

```sh
lax build /home/ebonnet/Bitbucket/lax/leighton-rao --replay
bash scripts/check-ram.sh
```

The compiled RAM checks run from standard zero memory and verify exact
certificate-coordinate conversion, min-plus updates, full Floyd–Warshall
execution, initialization from decoded dual coordinates, clipped edge
volumes, rational sums, root-distance vectors, metric costs, strict ball
membership, masked masses, both boundary orientations, active initialization,
residual graph reconstruction, root selection, complete seeded volumes,
mass-based orientation selection, complete radius-acceptance queries, grid/event candidate generation,
first-success radius search and restoration of the selected query,
positive-support counting, integer budget computation, exact growth constants,
and their combined initialization,
first-match scans, mask products, zero dimensions,
large rational words, and termination within the
stated fuel. Each check lists its physical input and expected output in
`checks/CertificateDecode.lean`, `checks/MinPlus.lean`, or
`checks/FloydWarshall.lean`, `checks/DualDistances.lean`,
`checks/RegionArithmetic.lean`, `checks/EdgePortion.lean`,
`checks/RootDistances.lean`, `checks/MetricCost.lean`, `checks/BallMass.lean`,
`checks/Boundary.lean`, `checks/Residual.lean`, `checks/Root.lean`,
`checks/Volume.lean`, `checks/RegionDirection.lean`, `checks/RegionQuery.lean`,
`checks/RadiusCandidates.lean`, `checks/RadiusSearch.lean`,
`checks/SupportBudget.lean`, `checks/RoundingConstants.lean`,
`checks/RoundingInit.lean`,
`checks/Find.lean`, and
`checks/ProductVector.lean`. The harness compiles
the native command to the registered word RAM; it does not substitute a host
implementation of the decoder.

Build artifacts use the existing shared mathlib and RAM dependencies.
