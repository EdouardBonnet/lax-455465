import Lax455465.ProductFlowCut
import Lax455465.UniformFlowCut
import Lax455465.DirectedProductFlowCut
import Lax455465.DirectedUniformFlowCut

namespace Lax455465Proofs.UniformCorollaries

open Lax455465.ProductNetwork Lax455465.ConcurrentFlow

private theorem supportCount_uniformWeight (n : ℕ) :
    supportCount (uniformWeight n) = n := by
  simp [supportCount, uniformWeight]

/--
---
conclusion: Lax455465.UniformFlowCut.sparsestCut_le_log_mul_maxFlow
---
The undirected uniform flow–cut bound follows from the undirected product
bound by assigning weight one to every vertex.

# Proof strategy

The support contains all vertices, so its cardinality is exactly the graph
order. Specialize the product theorem and retain its universal constant.

# Attribution

This is the uniform specialization of the product formulation in Section 2.3
of Leighton and Rao (1999). The product flow–cut theorem remains an assumption.
-/
theorem undirected_uniform_flow_cut :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℕ) (N : Network n), N.IsUndirected → 2 ≤ n →
        (sparsestCut N (uniformWeight n) : ℝ) ≤
          C * logFactor n * (maxFlow .undirected N (uniformWeight n) : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := Lax455465.ProductFlowCut.sparsestCut_le_log_mul_maxFlow
  refine ⟨C, hC, ?_⟩
  intro n N hN hn
  have hp : 2 ≤ supportCount (uniformWeight n) := by
    simpa only [supportCount_uniformWeight] using hn
  simpa only [supportCount_uniformWeight] using hbound n N (uniformWeight n) hN hp

/--
---
conclusion: Lax455465.DirectedUniformFlowCut.sparsestCut_le_log_mul_maxFlow
---
The directed uniform flow–cut bound follows from the directed product
bound by assigning weight one to every vertex.

# Proof strategy

The support cardinality equals the graph order. Specialize the product
theorem, preserving both the full directed demand convention and its constant.

# Attribution

This is the uniform specialization of Theorem 17 of Leighton and Rao (1999).
The directed product flow–cut theorem remains an assumption.
-/
theorem directed_uniform_flow_cut :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℕ) (N : Network n), 2 ≤ n →
        (sparsestCut N (uniformWeight n) : ℝ) ≤
          C * logFactor n * (maxFlow .directed N (uniformWeight n) : ℝ) := by
  obtain ⟨C, hC, hbound⟩ :=
    Lax455465.DirectedProductFlowCut.sparsestCut_le_log_mul_maxFlow
  refine ⟨C, hC, ?_⟩
  intro n N hn
  have hp : 2 ≤ supportCount (uniformWeight n) := by
    simpa only [supportCount_uniformWeight] using hn
  simpa only [supportCount_uniformWeight] using hbound n N (uniformWeight n) hp

end Lax455465Proofs.UniformCorollaries
