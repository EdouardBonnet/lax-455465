import Lax455465.ConcurrentFlow

/-!
---
title: The undirected uniform flow–cut theorem
type: theorem
---
There is a universal constant $C>0$ such that every undirected $n$-vertex
uniform multicommodity instance, $n\ge2$, satisfies
$$\mathcal S\le C\log_2(n)\,f^*.$$
Each unordered pair has unit demand. This is Theorem 2 of Leighton and Rao
(1999), with its elementary cut upper bound stated separately.

# Formalization notes

Uniform demands are product demands with all vertex weights one. This
statement is available as its own review unit; the proof package derives
it from the undirected product theorem.
-/

namespace Lax455465.UniformFlowCut

open Lax455465.ProductNetwork Lax455465.ConcurrentFlow

/-- Uniform concurrent flow loses at most a logarithmic factor relative to cuts. -/
axiom sparsestCut_le_log_mul_maxFlow :
  ∃ C : ℝ, 0 < C ∧
    ∀ (n : ℕ) (N : Network n), N.IsUndirected → 2 ≤ n →
      (sparsestCut N (uniformWeight n) : ℝ) ≤
        C * logFactor n * (maxFlow .undirected N (uniformWeight n) : ℝ)

end Lax455465.UniformFlowCut
