import Lax455465.RamProductFlowCut
import Lax455465.RamUndirectedSparsestCut
import Lax455465.RamDirectedSparsestCut
import Lax455465.RamUniformFlowCut
import Lax455465.RamDirectedUniformFlowCut

open scoped NNReal

namespace Lax455465Proofs.ProductCorollaries

open Lax455465.ProductNetwork Lax455465.ConcurrentFlow
open Lax455465.RationalEncoding Lax455465.FlowCutCertificate Lax759944.RamPolytime

/--
---
conclusion: Lax455465.RamUndirectedSparsestCut.exists_polynomial_time_sparse_cut
---
Specialize the general algorithm to undirected input words and symmetric
capacities. The program, resource bounds and joint output are unchanged.

# Proof strategy

Apply the general certificate guarantee with the undirected mode. The
symmetry implication is discharged by the input's symmetry hypothesis.
-/
theorem undirected_product :
  ∃ (solve : List ℕ → List ℕ) (C : ℝ), RamPolytime solve ∧ 0 < C ∧
    ∀ (n : ℕ) (I : RationalInstance n),
      I.network.IsUndirected → 2 ≤ supportCount I.weights →
      ∃ certificate : Certificate n,
        solve (encodeInput .undirected I) = encodeCertificate certificate ∧
        IsValid .undirected I C certificate := by
  obtain ⟨solve, C, htime, hC, hsolve⟩ :=
    Lax455465.RamProductFlowCut.exists_polynomial_time_flow_cut
  refine ⟨solve, C, htime, hC, ?_⟩
  intro n I hsym hp
  exact hsolve .undirected n I (fun _ => hsym) hp

/--
---
conclusion: Lax455465.RamDirectedSparsestCut.exists_polynomial_time_sparse_cut
---
Specialize the general algorithm to directed input words. Asymmetric
capacities require no symmetry assumption.

# Proof strategy

The implication conditioned on undirected mode has a false antecedent.
All certificate and execution guarantees are inherited directly.
-/
theorem directed_product :
  ∃ (solve : List ℕ → List ℕ) (C : ℝ), RamPolytime solve ∧ 0 < C ∧
    ∀ (n : ℕ) (I : RationalInstance n), 2 ≤ supportCount I.weights →
      ∃ certificate : Certificate n,
        solve (encodeInput .directed I) = encodeCertificate certificate ∧
        IsValid .directed I C certificate := by
  obtain ⟨solve, C, htime, hC, hsolve⟩ :=
    Lax455465.RamProductFlowCut.exists_polynomial_time_flow_cut
  refine ⟨solve, C, htime, hC, ?_⟩
  intro n I hp
  exact hsolve .directed n I (by intro h; cases h) hp

private theorem supportCount_of_uniform {n : ℕ} (I : RationalInstance n)
    (hweights : ∀ v, I.weight v = 1) : supportCount I.weights = n := by
  simp [supportCount, RationalInstance.weights, hweights]

/--
---
conclusion: Lax455465.RamUniformFlowCut.exists_polynomial_time_flow_cut
---
The undirected uniform algorithm is the product algorithm on all-one weights.

# Proof strategy

Every vertex belongs to the demand support, so its size is the input order.
Use the undirected product guarantee and rewrite its logarithmic factor.
-/
theorem undirected_uniform :
  ∃ (solve : List ℕ → List ℕ) (C : ℝ), RamPolytime solve ∧ 0 < C ∧
    ∀ (n : ℕ) (I : RationalInstance n),
      I.network.IsUndirected → (∀ v, I.weight v = 1) → 2 ≤ n →
      ∃ certificate : Certificate n,
        solve (encodeInput .undirected I) = encodeCertificate certificate ∧
        AdmissibleCut I.weights certificate.cut ∧
        IsArcConcurrentFlow .undirected I.network I.weights
          (certificate.flow.value : ℝ≥0) certificate.flow.flow ∧
        (ratioCost I.network I.weights certificate.cut : ℝ) ≤
          C * logFactor n * (certificate.flow.value : ℝ) := by
  obtain ⟨solve, C, htime, hC, hsolve⟩ :=
    Lax455465.RamUndirectedSparsestCut.exists_polynomial_time_sparse_cut
  refine ⟨solve, C, htime, hC, ?_⟩
  intro n I hsym hweights hn
  have hp := supportCount_of_uniform I hweights
  obtain ⟨certificate, hout, hvalid⟩ := hsolve n I hsym (by simpa [hp] using hn)
  refine ⟨certificate, hout, ?_⟩
  simpa only [IsValid, hp] using hvalid

/--
---
conclusion: Lax455465.RamDirectedUniformFlowCut.exists_polynomial_time_flow_cut
---
The directed uniform algorithm is the directed product algorithm on all-one
weights, with full unit demand for each distinct ordered pair.

# Proof strategy

Rewrite the demand-support cardinality to the input order in the directed
product certificate guarantee. The RAM program itself is retained.
-/
theorem directed_uniform :
  ∃ (solve : List ℕ → List ℕ) (C : ℝ), RamPolytime solve ∧ 0 < C ∧
    ∀ (n : ℕ) (I : RationalInstance n), (∀ v, I.weight v = 1) → 2 ≤ n →
      ∃ certificate : Certificate n,
        solve (encodeInput .directed I) = encodeCertificate certificate ∧
        AdmissibleCut I.weights certificate.cut ∧
        IsArcConcurrentFlow .directed I.network I.weights
          (certificate.flow.value : ℝ≥0) certificate.flow.flow ∧
        (ratioCost I.network I.weights certificate.cut : ℝ) ≤
          C * logFactor n * (certificate.flow.value : ℝ) := by
  obtain ⟨solve, C, htime, hC, hsolve⟩ :=
    Lax455465.RamDirectedSparsestCut.exists_polynomial_time_sparse_cut
  refine ⟨solve, C, htime, hC, ?_⟩
  intro n I hweights hn
  have hp := supportCount_of_uniform I hweights
  obtain ⟨certificate, hout, hvalid⟩ := hsolve n I (by simpa [hp] using hn)
  refine ⟨certificate, hout, ?_⟩
  simpa only [IsValid, hp] using hvalid

end Lax455465Proofs.ProductCorollaries
