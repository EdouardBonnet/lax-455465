import Lax455465.FlowCutCertificate

/-!
---
title: Deterministic directed uniform flow–cut algorithm
type: theorem
---
A deterministic polynomial-time word RAM returns a cut and a rational
uniform concurrent flow satisfying
$$\operatorname{ratio}(S)\le C\log_2(n)\,f$$
on every rational directed $n$-vertex instance with $n\ge2$.

# Formalization notes

All input weights equal one. The proof specializes the directed product
algorithm; every vertex has positive weight, so $p=n$. Its program, exact
output, and registered RAM polynomial-time guarantee are retained.
-/

open scoped NNReal

namespace Lax455465.RamDirectedUniformFlowCut

open Lax455465.ProductNetwork Lax455465.ConcurrentFlow
open Lax455465.RationalEncoding Lax455465.FlowCutCertificate Lax759944.RamPolytime

/-- The uniform directed specialization of the product algorithm. -/
axiom exists_polynomial_time_flow_cut :
  ∃ (solve : List ℕ → List ℕ) (C : ℝ), RamPolytime solve ∧ 0 < C ∧
    ∀ (n : ℕ) (I : RationalInstance n), (∀ v, I.weight v = 1) → 2 ≤ n →
      ∃ certificate : Certificate n,
        solve (encodeInput .directed I) = encodeCertificate certificate ∧
        AdmissibleCut I.weights certificate.cut ∧
        IsArcConcurrentFlow .directed I.network I.weights
          (certificate.flow.value : ℝ≥0) certificate.flow.flow ∧
        (ratioCost I.network I.weights certificate.cut : ℝ) ≤
          C * logFactor n * (certificate.flow.value : ℝ)

end Lax455465.RamDirectedUniformFlowCut
