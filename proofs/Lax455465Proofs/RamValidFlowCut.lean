import Lax455465Proofs.RamInputMetricCost
import Lax455465Proofs.RamRoundAndOutput
import Lax455465Proofs.FlowPrimalHeight

set_option maxRecDepth 16384
namespace Lax455465Proofs.RamValidFlowCut
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamFlowData
open Lax455465.RationalEncoding Lax455465.ProductNetwork Lax759944.BinaryWordEncoding
open Lax759944.RamPolytime Lax109476.LinearProgram
open scoped NNRat

set_option maxHeartbeats 6400000 in
/-- One fixed native program reads the original graph, invokes the registered
LP solver, constructs its metric, rounds a cut, and emits the matching public
flow–cut certificate. Both resource polynomials use the original binary input
size. This theorem covers valid inputs; totality on arbitrary words is separate. -/
theorem exists_program :
    ∃ (c : Com) (timeBound wordBound sourceTime : Polynomial ℕ),
      ∀ {n : ℕ} (kind : EdgeKind) (I : RationalInstance n),
        (kind=.undirected → I.network.IsUndirected) → 2 ≤ supportCount I.weights →
        ∀ W : ℕ, wordBound.eval (bitSize (encodeInput kind I)) ≤ W →
          Spec (2^W) (fun σ => σ.inp=(encodeInput kind I).length::encodeInput kind I ∧
            (encodeInput kind I).length ≤ (σ.arrs "input.data").length ∧
            2*n < (σ.arrs "flow.weights").length ∧ 2*(n*n) < (σ.arrs "flow.capacities").length ∧
            RamFlowLp.wordLength n < (σ.arrs "lp.word").length ∧
            (Lax109476.RationalEncoding.encodeProgram (DirectedFlowLP.program I)).length < (σ.arrs "vm.input").length ∧
            sourceTime.eval (bitSize (Lax109476.RationalEncoding.encodeProgram (DirectedFlowLP.program I))) < (σ.arrs "vm.addresses").length ∧
            sourceTime.eval (bitSize (Lax109476.RationalEncoding.encodeProgram (DirectedFlowLP.program I))) < (σ.arrs "vm.values").length ∧
            sourceTime.eval (bitSize (Lax109476.RationalEncoding.encodeProgram (DirectedFlowLP.program I))) < (σ.arrs "vm.output").length ∧
            2*columns n < (σ.arrs "flow.primal").length ∧ 2*rows n < (σ.arrs "flow.dual").length ∧
            2*(n*n) < (σ.arrs "metric.old").length ∧ 2*(n*n) < (σ.arrs "metric.new").length ∧
            RamRegionInvariant.Room n (RamRoundingInit.support I.weight) σ ∧ RamRegionCut.Room n σ ∧
            2*columns n < (σ.arrs "flow.converted").length ∧ σ.out=[]) c
            (fun _ τ => ∃ certificate : Lax455465.FlowCutCertificate.Certificate n,
              Lax455465.FlowCutCertificate.IsValid kind I 512 certificate ∧
              τ.out=Lax455465.FlowCutCertificate.encodeCertificate certificate)
            (timeBound.eval (bitSize (encodeInput kind I))) := by
  obtain ⟨c,T,WB,TB,sourceWord,hnoWrite,hsource⟩ := RamInputMetricCost.exists_program
  let metric := FlowDistanceBounds.widthBound sourceWord
  let primal := FlowPrimalHeight.bound sourceWord
  refine ⟨.seq c RamRoundAndOutput.command,T+RamRoundAndOutput.timeBound metric primal,
    WB+RamRoundAndOutput.wordBound metric primal,TB,?_⟩
  intro n kind I hsym hp W hW
  obtain ⟨z,y,hz,hy,hmatch,hfit,hcorrect⟩ := hsource kind I hp
  let d := RamDualDistances.result y hy.1
  have hmetric : MetricMatrix.rational d=RationalDistances.dualDistance y := RamDualDistances.rational_result y hy.1
  have hd : ∀ u v,LpInputSize.Height (2^(metric.eval (bitSize (encodeInput kind I)))) (d u v : ℚ) := by
    intro u v
    change LpInputSize.Height _ (MetricMatrix.rational d u v)
    rw [hmetric]
    exact FlowDistanceBounds.dual_polynomial_height sourceWord kind I z y hy.1 hfit (List.finRange n) u v
  have hzheight := FlowPrimalHeight.polynomial_height sourceWord kind I z y hfit
  have hsum : WB.eval (bitSize (encodeInput kind I))+
      (RamRoundAndOutput.wordBound metric primal).eval (bitSize (encodeInput kind I)) ≤ W := by
    simpa only [Polynomial.eval_add] using hW
  rintro σ ⟨hinp,hinput,hwroom,hcroom,hlproom,hvin,hva,hvv,hvo,hpr,hdu,hOld,hNew,hregion,hcut,hconverted,hout⟩
  obtain ⟨ν,r1,hdata,hn,hn2,hkind,hprimal,hdual,hdσ,hcost⟩ := hcorrect W (by omega) σ
    ⟨hinp,hinput,hwroom,hcroom,hlproom,hvin,hva,hvv,hvo,hpr,hdu,hOld,hNew⟩
  obtain ⟨τ,r2,pr⟩ := RamRoundAndOutput.command_spec metric primal kind I z y hz hy hmatch d hmetric hd hzheight
    hp hsym W (by omega) ν
    ⟨⟨hn,hn2,hdata.2.2.2.2.2.2.1,hdata.2.2.2.2.2.2.2,hdσ,hcost⟩,
      hregion.frame r1,hcut.frame r1,
      ⟨hkind,by simpa only [RamOptimalDecode.length_vector] using hdata.2.2.2.2.1,hprimal⟩,
      by rw [RamFrames.run_array_length r1]; exact hconverted,
      (r1.out_eq hnoWrite).trans hout⟩
  exact ⟨τ,(r1.seq r2).mono (by simp only [Polynomial.eval_add]; rfl),pr⟩

end Lax455465Proofs.RamValidFlowCut
