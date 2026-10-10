import Lax455465.ConcurrentFlow

/-!
---
title: The directed uniform flow–cut theorem
type: theorem
---
There is a universal constant $C>0$ such that every directed $n$-vertex
uniform multicommodity instance, $n\ge2$, satisfies
$$\mathcal S\le C\log_2(n)\,f^*.$$
Each distinct ordered pair has unit demand. This is Theorem 12 of Leighton
and Rao (1999), with the elementary upper bound stated separately.

# Formalization notes

The proof package specializes the directed product theorem to all-one
weights. The directed unit-demand convention differs from the
half-demand per direction used for undirected instances.
-/

namespace Lax455465.DirectedUniformFlowCut

open Lax455465.ProductNetwork Lax455465.ConcurrentFlow

/-- Directed uniform concurrent flow is within a logarithmic factor of cuts. -/
axiom sparsestCut_le_log_mul_maxFlow :
  ∃ C : ℝ, 0 < C ∧
    ∀ (n : ℕ) (N : Network n), 2 ≤ n →
      (sparsestCut N (uniformWeight n) : ℝ) ≤
        C * logFactor n * (maxFlow .directed N (uniformWeight n) : ℝ)

end Lax455465.DirectedUniformFlowCut
