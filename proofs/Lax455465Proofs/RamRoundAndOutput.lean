import Lax455465Proofs.RamUniformRounding
import Lax455465Proofs.RamOutputResources
import Lax455465Proofs.RuntimeCutCertificate

set_option maxRecDepth 16384
namespace Lax455465Proofs.RamRoundAndOutput
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState
open Lax455465.RationalEncoding Lax455465.ProductNetwork Lax759944.BinaryWordEncoding
open Lax109476.LinearProgram
open scoped NNRat

def command : Com := .seq RamMetricRounding.command RamJointOutput.command
noncomputable def timeBound (metric primal : Polynomial ℕ) : Polynomial ℕ :=
  RamRoundingResources.timeBound (RamRoundingResources.baseBound metric)+RamOutputResources.timeBound primal
noncomputable def wordBound (metric primal : Polynomial ℕ) : Polynomial ℕ :=
  RamRoundingResources.wordBound (RamRoundingResources.baseBound metric)+RamOutputResources.wordBound primal

theorem support_eq {n : ℕ} (I : RationalInstance n) : RamRoundingInit.support I.weight=supportCount I.weights := by
  have he : RamRoundingInit.support I.weight=RegionRounding.supportSize I := by
    unfold RamRoundingInit.support RegionRounding.supportSize
    congr 2
    funext v
    simp [RegionLoop.weights]
  exact he.trans (MetricRounding.supportSize_eq I)

set_option maxHeartbeats 6400000 in
/-- Starting from the actual matching LP vectors and their computed metric,
the fixed native suffix returns a valid public joint certificate, and its
physical output is exactly the encoding of that same certificate. -/
theorem command_spec (metric primal : Polynomial ℕ) {n : ℕ} (kind : EdgeKind) (I : RationalInstance n)
    (z : Fin (1+(n*n)*(n*n)) → ℚ) (y : Fin (n*n+2*((n*n)*n)) → ℚ)
    (hz : PrimalFeasible (DirectedFlowLP.program I) z) (hy : DualFeasible (DirectedFlowLP.program I) y)
    (hmatch : primalValue (DirectedFlowLP.program I) z=dualValue (DirectedFlowLP.program I) y)
    (d : MetricMatrix.Matrix n) (hmetric : MetricMatrix.rational d=RationalDistances.dualDistance y)
    (hd : ∀ u v,LpInputSize.Height (2^(metric.eval (bitSize (encodeInput kind I)))) (d u v : ℚ))
    (hzheight : ∀ i,LpInputSize.Height (2^(primal.eval (bitSize (encodeInput kind I)))) (z i))
    (hp : 2 ≤ supportCount I.weights) (hsym : kind=.undirected → I.network.IsUndirected)
    (W : ℕ) (hW : (wordBound metric primal).eval (bitSize (encodeInput kind I)) ≤ W) :
    Spec (2^W) (fun σ => RamMetricRounding.Input I d σ ∧
      RamRegionInvariant.Room n (RamRoundingInit.support I.weight) σ ∧ RamRegionCut.Room n σ ∧
      RamFlowConvert.Context kind (RamOptimalDecode.vector z hz.1) σ ∧
      2*(1+(n*n)*(n*n)) < (σ.arrs "flow.converted").length ∧ σ.out=[]) command
      (fun _ τ => ∃ certificate : Lax455465.FlowCutCertificate.Certificate n,
        Lax455465.FlowCutCertificate.IsValid kind I 512 certificate ∧
        τ.out=Lax455465.FlowCutCertificate.encodeCertificate certificate)
      ((timeBound metric primal).eval (bitSize (encodeInput kind I))) := by
  let L := bitSize (encodeInput kind I)
  have hsum : (RamRoundingResources.wordBound (RamRoundingResources.baseBound metric)).eval L+
      (RamOutputResources.wordBound primal).eval L ≤ W := by simpa only [wordBound,Polynomial.eval_add] using hW
  dsimp only [L] at hsum
  have hp' : 0 < RamRoundingInit.support I.weight := by rw [support_eq]; omega
  have ht : 0 < LargeBallRounding.total I := MetricRounding.total_positive I (by
    rw [MetricRounding.supportSize_eq]; omega)
  obtain ⟨_,hdiag,htri,hsep⟩ := RationalDistances.dualDistance_spec I y hy
  have hdiag' : ∀ v,d v v=0 := by
    intro v
    apply NNRat.coe_injective
    change MetricMatrix.rational d v v=0
    rw [hmetric,hdiag]
  have htri' : ∀ u v t,(d u t : ℚ) ≤ (d u v : ℚ)+(d v t : ℚ) := by
    intro u v t
    change MetricMatrix.rational d u t ≤ MetricMatrix.rational d u v+MetricMatrix.rational d v t
    rw [hmetric]
    exact htri u v t
  have hsep' : 1 ≤ LargeBallRounding.distanceSeparation I (MetricMatrix.rational d) := by
    rw [hmetric]
    simpa only [LargeBallRounding.distanceSeparation,DirectedFlowLP.Edge,Fintype.sum_prod_type] using hsep
  rintro σ ⟨hin,hregion,hcut,hprimal,hroom,hout⟩
  obtain ⟨ν,r1,S,hadm,hbound,hmask⟩ := RamUniformRounding.command_spec metric kind I d hd hp' ht hdiag' htri' hsep'
    W (by omega) σ ⟨hin,hregion,hcut⟩
  obtain ⟨τ,r2,p2⟩ := RamOutputResources.command_spec primal kind I S z hz.1 hzheight W (by omega) ν
    ⟨RamFlowConvert.frame r1 hprimal (by decide) (by decide),
      (r1.frame_var "metric.n" (by decide)).trans hin.nValue,hmask,
      by rw [RamFrames.run_array_length r1]; exact hroom,
      (r1.out_eq (by decide)).trans hout⟩
  refine ⟨τ,(r1.seq r2).mono (by simp only [timeBound,Polynomial.eval_add]; rfl),
    ⟨S,CertificatePostprocessing.convertFlow kind (CertificatePostprocessing.primalFlow z)⟩,?_,p2⟩
  exact RuntimeCutCertificate.certificate_valid kind I z y hz hy hmatch d hmetric S hadm
    (by simpa only [support_eq] using hbound) hp hsym

end Lax455465Proofs.RamRoundAndOutput
