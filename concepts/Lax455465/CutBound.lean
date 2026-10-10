import Lax455465.ConcurrentFlow

/-!
---
title: The cut upper bound on concurrent flow
type: theorem
---
For every product multicommodity instance with at least two positive-weight
vertices, the maximum concurrent flow is at most the sparsest-cut value:
$$f^*\le\mathcal S.$$
This holds for undirected and directed networks, with their respective
demand and capacity conventions.

# Formalization notes

The symmetry hypothesis is required only for undirected capacities. This
elementary upper bound is stated separately from the logarithmic converse,
so each has its own proof obligation.
-/

namespace Lax455465.CutBound

open Lax455465.ProductNetwork Lax455465.ConcurrentFlow

/-- No concurrent flow exceeds the capacity-to-demand ratio of a sparsest cut. -/
axiom maxFlow_le_sparsestCut :
  ∀ (kind : EdgeKind) (n : ℕ) (N : Network n) (π : VertexWeight n),
    (kind = .undirected → N.IsUndirected) → 2 ≤ supportCount π →
      maxFlow kind N π ≤ sparsestCut N π

end Lax455465.CutBound
