import Lax455465.RationalEncoding
import Lax455465.ShortPathFlow

/-!
---
title: Polynomial-time RAM construction of a uniform short-path flow
type: theorem
---
There is a polynomial-time word-RAM algorithm and universal constants $A,B>0$
such that, on every rational undirected uniform instance with $n\ge2$ and
positive sparsest-cut value $\mathcal S$, it returns a rational fractional
flow certificate meeting a common fraction $f$ of all demands, where
$$\mathcal S\le A\log_2(n)f,$$
and every path carrying flow has length at most
$$\frac{B C_{\max}\log_2(n)}{n\mathcal S}.$$

# Formalization notes

This states the algorithmic assertion accompanying Theorem 18 of Leighton
and Rao (1999). The same decoded certificate must satisfy capacities, every
commodity demand, the flow-value bound, and the path-length bound. Its exact
rational output is produced by a program certified by the registered RAM
polynomial-time predicate. All-one weights are required in the input encoding.
-/

open scoped NNReal

namespace Lax455465.RamUniformShortPathFlow

open Lax455465.ProductNetwork Lax455465.ConcurrentFlow
open Lax455465.ShortPathFlow Lax455465.RationalEncoding Lax759944.RamPolytime

/-- A polynomial-time RAM constructs a feasible uniform flow with the
value and path-length guarantees of Theorem 18. -/
axiom exists_polynomial_time_short_path_flow :
  ∃ (solve : List ℕ → List ℕ) (A B : ℝ),
    RamPolytime solve ∧ 0 < A ∧ 0 < B ∧
      ∀ (n : ℕ) (I : RationalInstance n),
        I.network.IsUndirected → (∀ v, I.weight v = 1) → 2 ≤ n →
          0 < sparsestCut I.network (uniformWeight n) →
            ∃ certificate : FlowCertificate n,
              solve (encodeInput .undirected I) = encodeFlow certificate ∧
              IsConcurrentFlow .undirected I.network (uniformWeight n)
                (certificate.value : ℝ≥0) certificate.flow ∧
              (sparsestCut I.network (uniformWeight n) : ℝ) ≤
                A * logFactor n * (certificate.value : ℝ) ∧
              HasPathLengthAtMost certificate.flow
                (B * (maxIncidentCapacity I.network : ℝ) * logFactor n /
                  ((n : ℝ) * (sparsestCut I.network (uniformWeight n) : ℝ)))

end Lax455465.RamUniformShortPathFlow
