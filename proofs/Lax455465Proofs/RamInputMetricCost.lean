import Lax455465Proofs.RamInputMetric
import Lax455465Proofs.RamMetricCostResources

namespace Lax455465Proofs.RamInputMetricCost

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamFlowData DirectedFlowLP
open Lax455465.RationalEncoding Lax455465.ProductNetwork
open Lax109476.LinearProgram Lax109476.RationalCertificates Lax759944.RamPolytime
open Lax759944.BinaryWordEncoding
open scoped NNRat

set_option maxHeartbeats 1600000 in
/-- A single fixed native command obtains the matching LP witnesses,
computes their exact shortest-distance metric, and sums its metric cost
from the physical source graph, with uniform polynomial resources. -/
theorem exists_program :
    ∃ (c : Com) (timeBound wordBound sourceTime sourceWord : Polynomial ℕ),
      c.NoWrite ∧ ∀ {n : ℕ} (kind : EdgeKind) (I : RationalInstance n), 2 ≤ supportCount I.weights →
        ∃ (z : Fin (columns n) → ℚ) (y : Fin (rows n) → ℚ)
          (hz : PrimalFeasible (program I) z) (hy : DualFeasible (program I) y),
          primalValue (program I) z = dualValue (program I) y ∧
          FitsInWords (sourceWord.eval (bitSize (Lax109476.RationalEncoding.encodeProgram (program I))))
            (Lax109476.RationalEncoding.encodeCertificate (.optimal z y)) ∧
          ∀ W : ℕ, wordBound.eval (bitSize (encodeInput kind I)) ≤ W →
            Spec (2^W) (fun σ => σ.inp = (encodeInput kind I).length :: encodeInput kind I ∧
              (encodeInput kind I).length ≤ (σ.arrs "input.data").length ∧
              2*n < (σ.arrs "flow.weights").length ∧ 2*(n*n) < (σ.arrs "flow.capacities").length ∧
              RamFlowLp.wordLength n < (σ.arrs "lp.word").length ∧
              (Lax109476.RationalEncoding.encodeProgram (program I)).length < (σ.arrs "vm.input").length ∧
              sourceTime.eval (bitSize (Lax109476.RationalEncoding.encodeProgram (program I))) < (σ.arrs "vm.addresses").length ∧
              sourceTime.eval (bitSize (Lax109476.RationalEncoding.encodeProgram (program I))) < (σ.arrs "vm.values").length ∧
              sourceTime.eval (bitSize (Lax109476.RationalEncoding.encodeProgram (program I))) < (σ.arrs "vm.output").length ∧
              2*columns n < (σ.arrs "flow.primal").length ∧ 2*rows n < (σ.arrs "flow.dual").length ∧
              2*(n*n) < (σ.arrs "metric.old").length ∧ 2*(n*n) < (σ.arrs "metric.new").length)
              c (fun _ τ => Data I τ ∧ τ.vars "metric.n" = n ∧ τ.vars "metric.n2" = n*n ∧
                τ.vars "flow.kind" = RamGraphHeader.tag kind ∧
                Prefix (RamUnsignedBuffer.encode (RamOptimalDecode.vector z hz.1)) "flow.primal" τ ∧
                Prefix (RamUnsignedBuffer.encode (RamOptimalDecode.vector y hy.1)) "flow.dual" τ ∧
                Prefix (RamUnsignedBuffer.encode (MetricMatrix.values (RamDualDistances.result y hy.1))) "metric.old" τ ∧
                RamUnsignedScalar.Stored "round.cost" (MetricCostData.cost I (RamDualDistances.result y hy.1)) τ)
              (timeBound.eval (bitSize (encodeInput kind I))) := by
  obtain ⟨c,T,WB,TB,sourceWord,hnoWrite,hsolver⟩ := RamInputMetric.exists_program
  let P := FlowDistanceBounds.widthBound sourceWord
  refine ⟨.seq c RamMetricCost.command,T+RamMetricCostResources.timeBound P,
    WB+RamMetricCostResources.wordBound P,TB,sourceWord,⟨hnoWrite,by decide⟩,?_⟩
  intro n kind I hp
  obtain ⟨z,y,hz,hy,hvalue,hfit,hcorrect⟩ := hsolver kind I hp
  refine ⟨z,y,hz,hy,hvalue,hfit,?_⟩
  intro W hW
  let L := bitSize (encodeInput kind I)
  let K := P.eval L
  let D := RamDualDistances.result y hy.1
  have hsum : WB.eval L+(RamMetricCostResources.wordBound P).eval L ≤ W := by
    simpa only [Polynomial.eval_add,L] using hW
  have hWB : WB.eval L ≤ W := by omega
  obtain ⟨hB,hindex⟩ := RamMetricCostResources.host_bound P kind I W (by
    have hh : (RamMetricCostResources.wordBound P).eval L ≤ W := by omega
    simpa only [L] using hh)
  have hheight : ∀ u v, LpInputSize.Height (2^K) (D u v : ℚ) := by
    intro u v
    change LpInputSize.Height (2^K) (MetricMatrix.rational D u v)
    rw [show MetricMatrix.rational D = RationalDistances.dualDistance y from RamDualDistances.rational_result y hy.1]
    exact FlowDistanceBounds.dual_polynomial_height sourceWord kind I z y hy.1 hfit (List.finRange n) u v
  rintro σ ⟨hinp,hinputRoom,hwroom,hcroom,hlproom,hvinput,hA,hV,hO,hpr,hdu,hOld,hNew⟩
  obtain ⟨ν,rlp,plp⟩ := hcorrect W hWB σ
    ⟨hinp,hinputRoom,hwroom,hcroom,hlproom,hvinput,hA,hV,hO,hpr,hdu,hOld,hNew⟩
  obtain ⟨τ,rcost,pcost⟩ := RamMetricCost.command_spec (2^W) kind I D K hheight hB hindex ν
    ⟨plp.2.2.1,plp.1.2.2.2.2.2.2.2,plp.2.2.2.2.2.2⟩
  have hcostBound := RamMetricCostResources.time_bound P kind I
  refine ⟨τ,(rlp.seq rcost).mono ?_,RamFlowData.frame rcost I plp.1 (by decide) (by decide),
    (rcost.frame_var "metric.n" (by decide)).trans plp.2.1,
    (rcost.frame_var "metric.n2" (by decide)).trans plp.2.2.1,
    (rcost.frame_var "flow.kind" (by decide)).trans plp.2.2.2.1,?_,?_,?_,pcost⟩
  · simp only [Polynomial.eval_add]
    dsimp only [K,L] at hcostBound ⊢
    omega
  · simpa only [Prefix,rcost.frame_arr "flow.primal" (by decide)] using plp.2.2.2.2.1
  · simpa only [Prefix,rcost.frame_arr "flow.dual" (by decide)] using plp.2.2.2.2.2.1
  · simpa only [Prefix,rcost.frame_arr "metric.old" (by decide)] using plp.2.2.2.2.2.2

end Lax455465Proofs.RamInputMetricCost
