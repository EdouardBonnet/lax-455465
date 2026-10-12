import Lax455465Proofs.RamRegionCut
import Lax455465Proofs.CertificatePostprocessing

open scoped BigOperators NNReal NNRat
namespace Lax455465Proofs.RuntimeCutCertificate
open Lax455465.RationalEncoding Lax455465.ProductNetwork Lax455465.ConcurrentFlow
open Lax455465.FlowCutCertificate Lax109476.LinearProgram RationalDistances CutSweeps

/-- Any shore with the proved integer-budget bound has the advertised
logarithmic approximation guarantee, independently of sweep tie-breaking. -/
theorem log_bound {n : ℕ} (I : RationalInstance n) (d : MetricMatrix.Matrix n) (S : Finset (Fin n))
    (hp : 2 ≤ supportCount I.weights)
    (hbound : ratioQ I S ≤ (288/5 : ℚ)*(RegionBudget.steps (supportCount I.weights) : ℚ)*
      RegionRounding.metricCost I (MetricMatrix.rational d)) :
    (ratioQ I S : ℝ) ≤ 512*logFactor (supportCount I.weights)*
      (RegionRounding.metricCost I (MetricMatrix.rational d) : ℝ) := by
  have hratioR := Rat.cast_le (K := ℝ).mpr hbound
  norm_num only [Rat.cast_mul,Rat.cast_div,Rat.cast_natCast,Rat.cast_ofNat] at hratioR
  have hlog := RegionBudget.steps_le_log (supportCount I.weights) hp
  have hlogpos : 0 ≤ Real.log (supportCount I.weights)/Real.log 2 := by positivity
  have hW : 0 ≤ (RegionRounding.metricCost I (MetricMatrix.rational d) : ℝ) := by
    exact_mod_cast RegionCharging.weight_nonnegative (fun u v => (I.capacity u v : ℚ)) (MetricMatrix.rational d)
      (fun _ _ => NNRat.coe_nonneg _) (fun _ _ => NNRat.coe_nonneg _)
  have hbudget := mul_le_mul_of_nonneg_left hlog (show (0 : ℝ) ≤ 288/5 by norm_num)
  have hbudgetW := mul_le_mul_of_nonneg_right hbudget hW
  have hlogW := mul_nonneg hlogpos hW
  unfold logFactor
  nlinarith

/-- The actual RAM-produced shore and the matching LP primal coordinates
form a public certificate. Undirected conversion halves arc amounts and
preserves the concurrent demand fraction. -/
theorem certificate_valid {n : ℕ} (kind : EdgeKind) (I : RationalInstance n)
    (z : Fin (1+(n*n)*(n*n)) → ℚ)
    (y : Fin (n*n+2*((n*n)*n)) → ℚ)
    (hz : PrimalFeasible (DirectedFlowLP.program I) z) (hy : DualFeasible (DirectedFlowLP.program I) y)
    (hmatch : primalValue (DirectedFlowLP.program I) z=dualValue (DirectedFlowLP.program I) y)
    (d : MetricMatrix.Matrix n) (hmetric : MetricMatrix.rational d=dualDistance y)
    (S : Finset (Fin n)) (hadm : admissibleQ I S)
    (hbound : ratioQ I S ≤ (288/5 : ℚ)*(RegionBudget.steps (supportCount I.weights) : ℚ)*
      RegionRounding.metricCost I (MetricMatrix.rational d))
    (hp : 2 ≤ supportCount I.weights) (hsym : kind=.undirected → I.network.IsUndirected) :
    IsValid kind I 512 ⟨S,CertificatePostprocessing.convertFlow kind (CertificatePostprocessing.primalFlow z)⟩ := by
  let f := z (DirectedFlowLP.variableIndex n (.inl 0))
  let x := fun a => z (DirectedFlowLP.variableIndex n (.inr a))
  have hrepr : DirectedFlowLP.vector f x=z := DirectedFlowBounds.vector_representation z
  have hfeasible : DirectedFlowLP.Feasible I f x := by
    rw [←hrepr,DirectedFlowLP.feasible_iff] at hz
    exact hz
  let F := ArcCertificates.certificate I f x hfeasible
  have hF := ArcCertificates.certificate_valid I f x hfeasible
  have hprimal : F=CertificatePostprocessing.primalFlow z := rfl
  have hvalue : (F.value : ℚ)=dualValue (DirectedFlowLP.program I) y := by
    rw [←hrepr,DirectedFlowLP.objective_value] at hmatch
    simpa only [F,ArcCertificates.certificate,Rat.coe_toNNRat f hfeasible.1] using hmatch
  have hratio := log_bound I d S hp hbound
  have hcost : (RegionRounding.metricCost I (MetricMatrix.rational d) : ℝ) ≤ ((F.value : ℚ) : ℝ) := by
    rw [hvalue,hmetric]
    exact Rat.cast_le.mpr (dualDistance_cost I y hy)
  have hlog : 0 ≤ logFactor (supportCount I.weights) := by
    unfold logFactor
    positivity
  have hratioF := hratio.trans (mul_le_mul_of_nonneg_left hcost (mul_nonneg (by norm_num : (0 : ℝ) ≤ 512) hlog))
  have hdirected : IsValid .directed I 512 ⟨S,F⟩ := by
    refine ⟨(admissibleQ_iff I S).mp hadm,hF,?_⟩
    rw [←ratioQ_cast]
    simpa only [Rat.cast_nnratCast] using hratioF
  rw [←hprimal]
  cases kind with
  | directed => exact hdirected
  | undirected => exact ⟨hdirected.1,UndirectedConversion.halve_valid I F (hsym rfl) hF,hdirected.2.2⟩

end Lax455465Proofs.RuntimeCutCertificate
