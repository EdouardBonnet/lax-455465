import Lax455465Proofs.MetricRounding
import Lax455465Proofs.ArcCertificates
import Lax455465Proofs.UndirectedConversion

open scoped BigOperators NNReal NNRat

namespace Lax455465Proofs.DualRounding

open Lax455465.RationalEncoding Lax455465.ProductNetwork Lax455465.ConcurrentFlow
open Lax455465.FlowCutCertificate Lax109476.LinearProgram RationalDistances CutSweeps

/-- The exact finite rational postprocessing applied to the flow LP's
returned dual coordinates. -/
def round {n : ℕ} (I : RationalInstance n)
    (y : Fin (n * n + 2 * ((n * n) * n)) → ℚ) : Option (Finset (Fin n)) :=
  MetricRounding.round I (dualDistance y)

theorem round_correct {n : ℕ} (I : RationalInstance n)
    (y : Fin (n * n + 2 * ((n * n) * n)) → ℚ)
    (hy : DualFeasible (DirectedFlowLP.program I) y) (hp : 2 ≤ supportCount I.weights) :
    ∃ S, round I y = some S ∧ admissibleQ I S ∧
      (ratioQ I S : ℝ) ≤ 512 * logFactor (supportCount I.weights) * ((dualValue (DirectedFlowLP.program I) y : ℚ) : ℝ) := by
  obtain ⟨hd, hdiag, htri, hsep⟩ := dualDistance_spec I y hy
  have hsep' : 1 ≤ LargeBallRounding.distanceSeparation I (dualDistance y) := by
    simpa only [LargeBallRounding.distanceSeparation, DirectedFlowLP.Edge, Fintype.sum_prod_type] using hsep
  obtain ⟨S, hs, hadm, hratio⟩ := MetricRounding.round_log_bound I (dualDistance y) hp hd hdiag hsep' htri
  refine ⟨S, hs, hadm, hratio.trans ?_⟩
  have hcost : (RegionRounding.metricCost I (dualDistance y) : ℝ) ≤
      ((dualValue (DirectedFlowLP.program I) y : ℚ) : ℝ) := Rat.cast_le.mpr (dualDistance_cost I y hy)
  have hlog : 0 ≤ logFactor (supportCount I.weights) := by
    unfold logFactor
    apply div_nonneg
    · apply Real.log_nonneg
      have hp' : (1 : ℕ) ≤ supportCount I.weights := by omega
      exact_mod_cast hp'
    · exact (Real.log_pos (by norm_num)).le
  exact mul_le_mul_of_nonneg_left hcost (mul_nonneg (by norm_num) hlog)

/-- The returned cut and matching directed flow form the required joint
certificate with one universal approximation constant. -/
theorem directed_certificate {n : ℕ} (I : RationalInstance n) (F : ArcCertificate n)
    (y : Fin (n * n + 2 * ((n * n) * n)) → ℚ)
    (hy : DualFeasible (DirectedFlowLP.program I) y) (hp : 2 ≤ supportCount I.weights)
    (hF : IsArcConcurrentFlow .directed I.network I.weights (F.value : ℝ≥0) F.flow)
    (hmatch : (F.value : ℚ) = dualValue (DirectedFlowLP.program I) y) :
    ∃ S, round I y = some S ∧ IsValid .directed I 512 ⟨S, F⟩ := by
  obtain ⟨S, hs, hadm, hratio⟩ := round_correct I y hy hp
  refine ⟨S, hs, (admissibleQ_iff I S).mp hadm, hF, ?_⟩
  rw [← ratioQ_cast]
  rw [← hmatch] at hratio
  simpa only [Rat.cast_nnratCast] using hratio

/-- The same cut works for symmetric shared capacities; halving the
arc amounts preserves the returned demand fraction and approximation. -/
theorem undirected_certificate {n : ℕ} (I : RationalInstance n) (F : ArcCertificate n)
    (y : Fin (n * n + 2 * ((n * n) * n)) → ℚ)
    (hy : DualFeasible (DirectedFlowLP.program I) y) (hp : 2 ≤ supportCount I.weights)
    (hsym : I.network.IsUndirected)
    (hF : IsArcConcurrentFlow .directed I.network I.weights (F.value : ℝ≥0) F.flow)
    (hmatch : (F.value : ℚ) = dualValue (DirectedFlowLP.program I) y) :
    ∃ S, round I y = some S ∧ IsValid .undirected I 512 ⟨S, UndirectedConversion.halve F⟩ := by
  obtain ⟨S, hs, hadm, _, hratio⟩ := directed_certificate I F y hy hp hF hmatch
  exact ⟨S, hs, hadm, UndirectedConversion.halve_valid I F hsym hF, hratio⟩

end Lax455465Proofs.DualRounding
