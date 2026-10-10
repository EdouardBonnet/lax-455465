import Lax455465.ConcurrentFlow

/-!
---
title: The logarithmic flow–cut gap is necessary
type: theorem
---
There are constants $c>0$ and $n_0\ge2$ such that, for every $n\ge n_0$,
an undirected $n$-vertex uniform instance with positive maximum concurrent
flow satisfies
$$c\log_2(n)\,f^*\le\mathcal S.$$
Consequently, the logarithmic factor in the uniform flow–cut theorem cannot
be replaced by a smaller asymptotic order.

# Formalization notes

This is the asymptotic content of Theorem 1 of Leighton and Rao (1999).
The explicit positive-flow condition rules out vacuous zero-capacity
examples. The threshold makes the big-$O$ statement precise without
small-order exceptions. The paper constructs the gap using bounded-degree
expanders; the statement does not prescribe a particular expander family.
-/

namespace Lax455465.TightFlowCutGap

open Lax455465.ProductNetwork Lax455465.ConcurrentFlow

/-- Uniform instances can require the full logarithmic flow–cut loss. -/
axiom exists_logarithmic_gap :
  ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, 2 ≤ n₀ ∧
    ∀ n : ℕ, n₀ ≤ n → ∃ N : Network n,
      N.IsUndirected ∧ 0 < maxFlow .undirected N (uniformWeight n) ∧
        c * logFactor n * (maxFlow .undirected N (uniformWeight n) : ℝ) ≤
          (sparsestCut N (uniformWeight n) : ℝ)

end Lax455465.TightFlowCutGap
