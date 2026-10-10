import Lax455465.ConcurrentFlow

/-!
---
title: The directed product flow–cut theorem
type: theorem
---
There is a universal constant $C>0$ such that every directed product
multicommodity instance with $p\ge2$ positive-weight vertices satisfies
$$\mathcal S\le C\log_2(p)\,f^*.$$
The demand from $u$ to $v$ is $\pi(u)\pi(v)$ for every distinct ordered
pair, and cuts count only the capacity of arcs leaving their first shore.

# Formalization notes

This is the support-size form of Theorem 17 of Leighton and Rao (1999),
obtained by combining Sections 2.3 and 2.4. The demands are symmetric,
but the capacities need not be. It makes no claim about arbitrary
nonproduct directed demands. There are $p(p-1)$ positive ordered
commodities, so the bound is equivalent to the paper's $O(\log k)$ form.
-/

namespace Lax455465.DirectedProductFlowCut

open Lax455465.ProductNetwork Lax455465.ConcurrentFlow

/-- The logarithmic converse to the directed cut bound for product demands. -/
axiom sparsestCut_le_log_mul_maxFlow :
  ∃ C : ℝ, 0 < C ∧
    ∀ (n : ℕ) (N : Network n) (π : VertexWeight n),
      2 ≤ supportCount π →
        (sparsestCut N π : ℝ) ≤
          C * logFactor (supportCount π) * (maxFlow .directed N π : ℝ)

end Lax455465.DirectedProductFlowCut
