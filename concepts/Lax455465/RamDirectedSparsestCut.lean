import Lax455465.RationalEncoding

/-!
---
title: Polynomial-time RAM construction of a directed sparse cut
type: theorem
---
There is a polynomial-time word-RAM algorithm and a universal constant $C>0$
such that, on every rational directed product instance with $p\ge2$
positive-weight vertices, the algorithm returns a cut of positive demand with
ratio cost at most $C\log_2(p)f^*$.

Together with the directed cut upper bound, this gives an $O(\log p)$
approximation algorithm for directed product sparsest cut.

# Formalization notes

This is the constructive directed guarantee of Sections 2.3–2.4 and 3.1
of Leighton and Rao (1999). The cut counts only outgoing arcs. Capacities
need not be symmetric; demands have the directed product convention.
The exact output and polynomial-time guarantee use the same encoding and
registered RAM predicate as the undirected algorithm.
-/

namespace Lax455465.RamDirectedSparsestCut

open Lax455465.ProductNetwork Lax455465.ConcurrentFlow Lax455465.RationalEncoding
open Lax759944.RamPolytime

/-- A polynomial-time RAM returns a directed product cut within a logarithmic
factor of the concurrent-flow optimum. -/
axiom exists_polynomial_time_sparse_cut :
  ∃ (solve : List ℕ → List ℕ) (C : ℝ), RamPolytime solve ∧ 0 < C ∧
    ∀ (n : ℕ) (I : RationalInstance n), 2 ≤ supportCount I.weights →
      ∃ S : Finset (Fin n),
        solve (encodeInput .directed I) = encodeCut S ∧
        AdmissibleCut I.weights S ∧
        (ratioCost I.network I.weights S : ℝ) ≤
          C * logFactor (supportCount I.weights) *
            (maxFlow .directed I.network I.weights : ℝ)

end Lax455465.RamDirectedSparsestCut
