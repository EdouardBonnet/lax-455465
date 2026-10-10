# Leighton–Rao flow–cut submission

Prepared submission `lax-455465`, based on Tom Leighton and Satish Rao,
*Multicommodity Max-Flow Min-Cut Theorems and Their Use in Designing
Approximation Algorithms*, JACM 46(6), 787–832 (1999),
[doi:10.1145/331524.331526](https://doi.org/10.1145/331524.331526).

The local reference PDF is `leighton-rao.pdf`. It is ignored by git and is
not part of the Apache-licensed submission source.

## Scope and proof status

| Source | Concept | Status |
| --- | --- | --- |
| Section 1.2; upper bounds in Theorems 2, 7, 12, 17 | `CutBound` | Open |
| Theorem 1 | `TightFlowCutGap` | Open |
| Theorem 2 | `UniformFlowCut` | Proved assuming `ProductFlowCut` |
| Section 2.3, Theorem 7 | `ProductFlowCut` | Open |
| Theorem 12 | `DirectedUniformFlowCut` | Proved assuming `DirectedProductFlowCut` |
| Theorem 17 | `DirectedProductFlowCut` | Open |
| Theorem 18 | `UniformShortPathTheorem` | Open |
| Sections 2.2–2.3 and 3.1: constructive sparse-cut guarantee | `RamUndirectedSparsestCut` | Open |
| Sections 2.3–2.4 and 3.1: directed constructive guarantee | `RamDirectedSparsestCut` | Open |
| Algorithmic construction accompanying Theorem 18 | `RamUniformShortPathFlow` | Open |

Definitions are organized into `ProductNetwork`, `ConcurrentFlow`,
`ShortPathFlow`, and `RationalEncoding`. The submission covers the headline
flow–cut results in Section 2 and their constructive cut guarantees. The
separate applications in Section 3 and the unnumbered extensions of
Theorem 18 to other demand models are outside this scope.

The proof network records exactly two conditional proofs: each uniform
converse depends on its product counterpart. This is a specialization of
the paper's statements; the paper itself develops the uniform case first.
No substantive flow–cut theorem has been discharged from background axioms.
Open statements are declared as Lax concept axioms, with no `sorry` proofs.

## Mathematical conventions

- Undirected edges share capacity between both directions. Each ordered
  pair has half the unordered-pair demand, as in footnotes 2 and 7.
- Directed arcs have separate capacities. Each ordered pair has full
  product demand, as in Section 2.4. The directed demand matrix is symmetric;
  its capacity matrix may be asymmetric.
- Product bounds use the number `p` of positive-weight vertices and
  `log₂ p`. The undirected paper's `log k` shorthand is not used at `p = 2`,
  when there is only one unordered commodity. Zero-weight transit vertices
  are permitted.
- Sparsest cuts range only over cuts of positive demand. All flow–cut
  statements require at least two positive-weight vertices; uniform
  statements require `n ≥ 2`.
- The short-path theorem requires positive sparsest-cut value and bounds
  the number of edges on every path carrying positive flow.
- The lower bound uses universal constants and an explicit asymptotic
  threshold, with positive maximum flow to exclude trivial zero examples.

## Existing RAM dependency

The algorithmic concepts use `Lax759944.RamPolytime.RamPolytime`, pinned to
the registered RAM–Turing submission:

```text
https://github.com/szymtor/RAM-TM
134e398cef46599371df99f10c9007bc34ba3868
concepts
```

That predicate uses the registered word RAM `Lax808846`, pinned transitively
to `https://github.com/lax-archive/lax-submissions` at
`9394e531cc51cb67a0214bca3f9264dfe97ba5c7`, folder `word-ram/concepts`.
Polynomial time is measured in the binary size of the rational input, with
one uniform program and polynomial bounds on both sufficient word length
and executed instructions. Each theorem requires exact encoded output.

Input and certificate formats are documented in `RationalEncoding`. In
particular, rational inputs retain their denominators; arithmetic on arbitrarily
large input integers is not silently treated as constant-cost computation.

## Validation

```sh
lax build /home/ebonnet/Bitbucket/lax/leighton-rao --replay
```

The repository is local. Publication and registration are separate steps.

Validation on 2026-10-10: `lax build --replay` passed, inspecting 14 concepts
and two conditional proofs. Both registered dependencies resolved successfully.
