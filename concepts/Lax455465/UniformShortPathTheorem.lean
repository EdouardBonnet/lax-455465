import Lax455465.ShortPathFlow

/-!
---
title: The uniform short-path flow theorem
type: theorem
---
There are universal constants $A,B>0$ such that every undirected $n$-vertex
uniform instance with positive sparsest-cut value $\mathcal S$ admits a
feasible concurrent flow of value
$$f\ge\frac{\mathcal S}{A\log_2 n}$$
using only paths of length at most
$$\frac{B C_{\max}\log_2 n}{n\mathcal S}.$$
This is Theorem 18 of Leighton and Rao (1999).

# Formalization notes

The flow-value inequality is written without division; the path-length
inequality retains the paper's bound. Both guarantees concern the same
flow witness. The positive-cut hypothesis makes the denominator meaningful;
zero-cut instances admit the empty flow. Algorithmic construction on
rational instances is stated separately over the existing RAM model.
-/

open scoped NNReal

namespace Lax455465.UniformShortPathTheorem

open Lax455465.ProductNetwork Lax455465.ConcurrentFlow Lax455465.ShortPathFlow

/-- A logarithmically large uniform flow can be routed on short paths. -/
axiom exists_short_path_flow :
  ∃ A B : ℝ, 0 < A ∧ 0 < B ∧
    ∀ (n : ℕ) (N : Network n), N.IsUndirected → 2 ≤ n →
      0 < sparsestCut N (uniformWeight n) →
        ∃ (f : ℝ≥0) (F : PathFlow n),
          IsConcurrentFlow .undirected N (uniformWeight n) f F ∧
          (sparsestCut N (uniformWeight n) : ℝ) ≤ A * logFactor n * (f : ℝ) ∧
          HasPathLengthAtMost F
            (B * (maxIncidentCapacity N : ℝ) * logFactor n /
              ((n : ℝ) * (sparsestCut N (uniformWeight n) : ℝ)))

end Lax455465.UniformShortPathTheorem
