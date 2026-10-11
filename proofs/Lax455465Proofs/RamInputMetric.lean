import Lax455465Proofs.RamInputOptimal
import Lax455465Proofs.RamDualDistances
import Lax455465Proofs.RamDistanceResources

namespace Lax455465Proofs.RamInputMetric

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamFlowData DirectedFlowLP
open Lax455465.RationalEncoding Lax455465.ProductNetwork
open Lax109476.LinearProgram Lax109476.RationalCertificates Lax759944.RamPolytime
open Lax759944.BinaryWordEncoding
open scoped NNRat

set_option maxHeartbeats 1600000 in
/-- The native LP and shortest-distance stages compose with uniform
polynomial resources from the physical source graph alone. The metric and
flow buffers contain the actual decoded witnesses, not chosen oracle data. -/
theorem exists_program :
    ∃ (c : Com) (timeBound wordBound sourceTime sourceWord : Polynomial ℕ),
      ∀ {n : ℕ} (kind : EdgeKind) (I : RationalInstance n), 2 ≤ supportCount I.weights →
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
              c (fun _ τ => Data I τ ∧ τ.vars "flow.kind" = RamGraphHeader.tag kind ∧
                Prefix (RamUnsignedBuffer.encode (RamOptimalDecode.vector z hz.1)) "flow.primal" τ ∧
                Prefix (RamUnsignedBuffer.encode (RamOptimalDecode.vector y hy.1)) "flow.dual" τ ∧
                Prefix (RamUnsignedBuffer.encode (MetricMatrix.values (RamDualDistances.result y hy.1))) "metric.old" τ)
              (timeBound.eval (bitSize (encodeInput kind I))) := by
  obtain ⟨c,T,WB,TB,sourceWord,hsolver⟩ := RamInputOptimal.exists_program
  let initTime : Polynomial ℕ := Polynomial.C 62*(Polynomial.X+Polynomial.C 1)^3
  let words : Polynomial ℕ := WB+Polynomial.C 2*FlowDistanceBounds.widthBound sourceWord+
    LpInputSize.sizeBound+Polynomial.C 20
  refine ⟨.seq c RamDualDistances.command,T+RamDistanceResources.timeBound sourceWord+initTime,
    words,TB,sourceWord,?_⟩
  intro n kind I hp
  obtain ⟨z,y,hz,hy,hvalue,hfit,hcorrect⟩ := hsolver kind I hp
  refine ⟨z,y,hz,hy,hvalue,hfit,?_⟩
  intro W hW
  let L := bitSize (encodeInput kind I)
  let S := LpInputSize.sizeBound.eval L
  let K := (FlowDistanceBounds.widthBound sourceWord).eval L
  let w := sourceWord.eval (bitSize (Lax109476.RationalEncoding.encodeProgram (program I)))
  have hsum : WB.eval L+2*K+S+20 ≤ W := by simpa [words,L,S,K] using hW
  have hWB : WB.eval L ≤ W := by omega
  obtain ⟨hB,hn,hn2,hindex⟩ := RamDistanceResources.host_bound sourceWord kind I W (by
    have hh : 2*K+S+20 ≤ W := by omega
    simpa only [K,S,L] using hh)
  have hyfit : FitsInWords w (Lax109476.RationalEncoding.encodeVector y) := by
    intro x hx
    exact hfit x (by simp only [Lax109476.RationalEncoding.encodeCertificate,List.mem_append]; exact Or.inr hx)
  have hyheight := FlowDistanceBounds.vector_height w y hyfit
  rintro σ ⟨hinp,hinputRoom,hwroom,hcroom,hlproom,hvinput,hA,hV,hO,hpr,hdu,hOld,hNew⟩
  obtain ⟨ν,rlp,plp⟩ := hcorrect W hWB σ
    ⟨hinp,hinputRoom,hwroom,hcroom,hlproom,hvinput,hA,hV,hO,hpr,hdu⟩
  obtain ⟨τ,rdist,pdist⟩ := RamDualDistances.command_spec (2^W) w y hy.1 hB hn hn2 hindex
    (fun i => (hyheight i).1) (fun i => (hyheight i).2) ν
    ⟨plp.1.1,plp.1.2.1,plp.2.2.2.1,
      by rwa [RamFrames.run_array_length rlp "metric.old"],
      by rwa [RamFrames.run_array_length rlp "metric.new"]⟩
  have hinitCost : 50*(n*n)+12 ≤ initTime.eval L := by
    have hnL : n ≤ L := LpInputSize.input_dimension kind I
    have hncube : n*n ≤ (L+1)^3 := by
      calc
        _ ≤ (L+1)^2 := by nlinarith
        _ ≤ _ := Nat.pow_le_pow_right (by omega) (by decide)
    have hpositive : 1 ≤ (L+1)^3 := Nat.succ_le_iff.mpr (pow_pos (by omega) 3)
    simp only [initTime,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,
      Polynomial.eval_add,Polynomial.eval_X]
    omega
  have hdistCost := RamDistanceResources.time_bound sourceWord kind I
  change n*((72*(w*(n*n+1))+324)*(n*n)+22)+10 ≤ (RamDistanceResources.timeBound sourceWord).eval L at hdistCost
  refine ⟨τ,(rlp.seq rdist).mono ?_,RamFlowData.frame rdist I plp.1 (by decide) (by decide),
    (rdist.frame_var "flow.kind" (by decide)).trans plp.2.1,?_,?_,pdist.2.2⟩
  · simp only [Polynomial.eval_add]
    dsimp only [L,w] at hinitCost hdistCost ⊢
    omega
  · simpa only [Prefix,rdist.frame_arr "flow.primal" (by decide)] using plp.2.2.1
  · simpa only [Prefix,rdist.frame_arr "flow.dual" (by decide)] using plp.2.2.2.1

end Lax455465Proofs.RamInputMetric
