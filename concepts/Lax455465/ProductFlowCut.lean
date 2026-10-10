import Lax455465.ConcurrentFlow

/-!
---
title: The undirected product flow–cut theorem
type: theorem
---
There is a universal constant $C>0$ such that every undirected product
multicommodity instance with $p\ge2$ positive-weight vertices satisfies
$$\mathcal S\le C\log_2(p)\,f^*.$$
Together with the cut upper bound, this places maximum concurrent flow
within a logarithmic factor of the sparsest cut.

# Formalization notes

This is the bound proved in Section 2.3 of Leighton and Rao (1999), yielding
their Theorem 7. The proof controls $\log p$; their displayed $\log k$
formulation uses $k=\binom p2$. We state the sharper support-size form,
which also covers $p=2$. Zero-weight vertices may carry transit flow, and
capacities and weights may be arbitrary nonnegative reals. The constant
is quantified before the instance. Weight normalization is unnecessary
because scaling all weights scales both $\mathcal S$ and $f^*$ equally.
-/

namespace Lax455465.ProductFlowCut

open Lax455465.ProductNetwork Lax455465.ConcurrentFlow

/-- The logarithmic converse to the cut bound for undirected product demands. -/
axiom sparsestCut_le_log_mul_maxFlow :
  ∃ C : ℝ, 0 < C ∧
    ∀ (n : ℕ) (N : Network n) (π : VertexWeight n),
      N.IsUndirected → 2 ≤ supportCount π →
        (sparsestCut N π : ℝ) ≤
          C * logFactor (supportCount π) * (maxFlow .undirected N π : ℝ)

end Lax455465.ProductFlowCut
