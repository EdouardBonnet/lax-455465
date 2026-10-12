import Lax455465Proofs.RamShortExtractionBounds
import Lax455465Proofs.ResidualInitialization
import Lax455465Proofs.RamLayeredPrimalDecode
import Lax455465Proofs.RamLayeredHostWidth
import Lax455465Proofs.LayeredOptimalCertificate

set_option maxRecDepth 16384
namespace Lax455465Proofs.RamShortFinish
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState
open LayeredFlowLP LayeredFlowDual LayeredFlowFeasibility LayeredLpFlat
open Lax455465.RationalEncoding Lax759944.BinaryWordEncoding Lax759944.RamPolytime
open scoped NNRat NNReal

def command : Com := .seq RamLayeredPrimalDecode.command RamShortExtraction.command

noncomputable def residualWidth (WB : Polynomial ℕ) : Polynomial ℕ :=
  (WB.comp LayeredLpSize.sizeBound+Polynomial.C 1)*(LayeredLpSize.sizeBound+Polynomial.C 2)
noncomputable def wordBound (WB : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C 2*residualWidth WB+Polynomial.C 64*(LayeredLpSize.sizeBound+Polynomial.C 1)^4+Polynomial.C 8
noncomputable def timeBound (WB : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C 39*LayeredLpSize.sizeBound+Polynomial.C 12+
    Polynomial.C 4096*(residualWidth WB+Polynomial.C 1)*(LayeredLpSize.sizeBound+Polynomial.C 1)^6

theorem dimensions {n : ℕ} (I : RationalInstance n) (L : ℕ) (hn : 2≤n) (hL : L≤n) :
    let S:=LayeredLpSize.sizeBound.eval (bitSize (encodeInput .undirected I))
    n≤S ∧ L≤S ∧ n*n≤S ∧ L*(n*n)≤S ∧ columns n L≤S := by
  dsimp only
  let S:=LayeredLpSize.sizeBound.eval (bitSize (encodeInput .undirected I))
  have hlen : LayeredLpSize.wordLength n L≤S := by
    rw [←LayeredLpSize.program_length I]
    exact (WordSize.length_le _).trans (LayeredLpSize.polynomial_size .undirected I L hL)
  have hr : rows n L≤S := by dsimp only [LayeredLpSize.wordLength] at hlen; omega
  have hc : columns n L≤S := by dsimp only [LayeredLpSize.wordLength] at hlen; omega
  have hn2r : n*n≤rows n L := by dsimp only [rows]; omega
  have hn2one : 1≤n*n := by nlinarith only [hn]
  have hn2 : n*n≤S := hn2r.trans hr
  have hnS : n≤S := by nlinarith only [hn,hn2]
  have hLA : L*(n*n)≤S := by
    have hh:=Nat.mul_le_mul_right (L*(n*n)) hn2one
    dsimp only [columns] at hc
    nlinarith only [hh,hc]
  exact ⟨hnS,hL.trans hnS,hn2,hLA,hc⟩

/-- Uniform execution and polynomial resources for decoding and extracting
the exact selected LP certificate. The denominator lattice is only a proof invariant. -/
theorem command_spec (WB : Polynomial ℕ) {n : ℕ} (I : RationalInstance n) (L : ℕ)
    (f : ℚ≥0) (x : Arc n L → ℚ) (y : Dual n L) (hn : 2≤n) (hL : 1≤L) (hLn : L≤n)
    (hf : Feasible I (f : ℚ) x)
    (hfit : FitsInWords (WB.eval (bitSize (Lax109476.RationalEncoding.encodeProgram (program I L))))
      (Lax109476.RationalEncoding.encodeCertificate (.optimal (vector (f : ℚ) x) y)))
    (W : ℕ) (hW : (wordBound WB).eval (bitSize (encodeInput .undirected I))≤W) :
    let S:=LayeredLpSize.sizeBound.eval (bitSize (encodeInput .undirected I))
    Spec (2^W) (fun σ => RamLayeredData.Data I L σ ∧
      Prefix (Lax109476.RationalEncoding.encodeCertificate (.optimal (vector (f : ℚ) x) y)) "vm.output" σ ∧
      2*S<(σ.arrs "flow.primal").length ∧ S+1<(σ.arrs "short.raw").length ∧
      S+1<(σ.arrs "short.simple").length ∧ RamShortExtractionBounds.space S<(σ.arrs "short.output").length ∧ σ.out=[])
      command (fun _ τ => ∃ rs : PathRecordBuffer.Records n,τ.out=encodeFlow ⟨f,rs⟩ ∧
        Lax455465.ConcurrentFlow.IsConcurrentFlow .undirected I.network (Lax455465.ProductNetwork.uniformWeight n)
          (f : ℝ≥0) (FlowCertificate.flow ⟨f,rs⟩) ∧
        Lax455465.ShortPathFlow.HasPathLengthAtMost (FlowCertificate.flow ⟨f,rs⟩) (L : ℝ))
      ((timeBound WB).eval (bitSize (encodeInput .undirected I))) := by
  dsimp only
  let b:=bitSize (encodeInput .undirected I)
  let S:=LayeredLpSize.sizeBound.eval b
  let w:=WB.eval S
  let r:=(w+1)*(S+2)
  have hdims:=dimensions I L hn hLn
  change n≤S ∧ L≤S ∧ n*n≤S ∧ L*(n*n)≤S ∧ columns n L≤S at hdims
  obtain ⟨hnS,hLS,hn2S,hLAS,hcS⟩:=hdims
  have hs : bitSize (Lax109476.RationalEncoding.encodeProgram (program I L))≤S :=
    LayeredLpSize.polynomial_size .undirected I L hLn
  have hwords : ∀ k∈Lax109476.RationalEncoding.encodeCertificate (.optimal (vector (f : ℚ) x) y),k<2^w := by
    intro k hk
    exact (hfit k hk).trans_le (Nat.pow_le_pow_right (by decide) (RamFlowSolverBounds.eval_mono WB hs))
  have hz : ∀ j,0≤vector (f : ℚ) x j := (feasible_iff I (f : ℚ) x).mpr hf |>.1
  let q : LayeredPathSweep.Coordinate n L → ℚ≥0 := fun j => ⟨vector (f : ℚ) x j,hz j⟩
  have hv : RamOptimalDecode.vector (vector (f : ℚ) x) hz=List.ofFn q := rfl
  have hq0 : q 0=f := by
    apply Subtype.ext
    change vector (f : ℚ) x 0=(f : ℚ)
    exact LayeredOptimalCertificate.vector_zero (f : ℚ) x
  have hqarc : LayeredWalkState.arc q=x := by
    funext a
    simp only [LayeredWalkState.arc,q,NNRat.coe_mk,vector,Equiv.symm_apply_apply]
  have hvectorwords : ∀ k∈Lax109476.RationalEncoding.encodeVector (vector (f : ℚ) x),k<2^w := by
    intro k hk
    exact hwords k (by simp only [Lax109476.RationalEncoding.encodeCertificate,List.mem_append]; exact Or.inl (Or.inr hk))
  obtain ⟨hnum,hden⟩:=RamOptimalDecode.vector_fits (2^w) (vector (f : ℚ) x) hz hvectorwords
  have hqn (j) : (q j).num≤2^w := (hnum _ (List.mem_ofFn.mpr ⟨j,rfl⟩)).le
  have hqd (j) : (q j).den≤2^w := (hden _ (List.mem_ofFn.mpr ⟨j,rfl⟩)).le
  let D:=ResidualInitialization.denominator q
  let H:=ResidualInitialization.height w
  have hD : 0<D := ResidualInitialization.denominator_pos q
  have hH : 1≤H := Nat.succ_le_of_lt (Nat.two_pow_pos _)
  have hM : H*D≤2^r := ResidualInitialization.residual_height q w S hcS hqn hqd
  obtain ⟨hqb,hab⟩:=ResidualInitialization.bounded q w hqn hqd
  have hW' : RamHostBounds.sufficient r 0 0 (RamShortExtractionBounds.space S)≤W := by
    simpa only [wordBound,residualWidth,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
      Polynomial.eval_pow,Polynomial.eval_comp,RamHostBounds.sufficient,RamShortExtractionBounds.space,
      Nat.add_zero,r,w,S,b] using hW
  obtain ⟨hB,_,_,hspace⟩:=RamHostBounds.sufficient_bounds r 0 0 (RamShortExtractionBounds.space S) W hW'
  have hBM : 2*(H*D)^2+3<2^W :=
    (Nat.add_le_add_right (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hM 2)) 3).trans_lt hB
  have hpow : 2^w<2^W := by
    have hwM : w≤r := by dsimp only [r]; nlinarith
    have hp:=Nat.pow_le_pow_right (show 1≤(2 : ℕ) by decide) hwM
    have hmb : 2^r<2^W := (show 2^r≤2*(2^r)^2+3 by nlinarith only [Nat.two_pow_pos r]).trans_lt hB
    exact hp.trans_lt hmb
  obtain ⟨hshape,hreserve,hcount,houtlen⟩:=RamShortExtractionBounds.space_bounds n L S hnS hLS hn2S hLAS hcS
  have h3 : 3<2^W := by omega
  rintro σ ⟨hd,hp,hpr,hraw,hsimple,hout,houtσ⟩
  change 2*S<(σ.arrs "flow.primal").length at hpr
  change S+1<(σ.arrs "short.raw").length at hraw
  change S+1<(σ.arrs "short.simple").length at hsimple
  change RamShortExtractionBounds.space S<(σ.arrs "short.output").length at hout
  have hscalar : 3*S+4≤RamShortExtractionBounds.space S := by
    dsimp only [RamShortExtractionBounds.space]
    nlinarith only [Nat.zero_le (S^3),Nat.zero_le (S^2)]
  obtain ⟨ν,r1,p1⟩:=RamLayeredPrimalDecode.command_spec (2^W) I (vector (f : ℚ) x) y hz h3
    (show 1+3*columns n L+3<2^W from
      (show 1+3*columns n L+3≤3*S+4 by omega).trans_lt (hscalar.trans_lt (by omega)))
    (fun q hq => (hnum q hq).trans hpow) (fun q hq => (hden q hq).trans hpow) σ
    ⟨hd,hp,(Nat.mul_le_mul_left 2 hcS).trans_lt hpr⟩
  have hdata : RamExtractionData.Data q ν := by
    refine ⟨p1.1.order,p1.1.square,p1.1.layer,p1.1.layerArcs,p1.1.columnCount,?_,?_,?_⟩
    · simpa only [hv] using p1.2
    · rw [RamFrames.run_array_length r1 "short.raw"]
      omega
    · rw [RamFrames.run_array_length r1 "short.simple"]
      omega
  obtain ⟨τ,r2,q',rs,hm,he,hflow,hlen⟩:=RamShortExtraction.command_spec (2^W) D H I q (by omega) hL hD hH hBM
    (hshape.trans_lt (by omega)) (hreserve.trans_lt (by omega)) (hcount.trans_lt (by omega)) hqb hab
    (by simpa only [hq0,hqarc] using hf) ν
    ⟨hdata,by rw [RamFrames.run_array_length r1 "short.output"]; exact hreserve.trans_lt hout,
      (r1.out_eq (by decide)).trans houtσ⟩
  refine ⟨τ,(r1.seq r2).mono ?_,rs,by simpa only [hq0] using he,by simpa only [hq0] using hflow,
    by simpa only [hq0] using hlen⟩
  have hc:=RamShortExtractionBounds.cost_bound n L S (H*D) r hnS hLS hn2S hcS hM
  simp only [timeBound,residualWidth,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
    Polynomial.eval_pow,Polynomial.eval_comp]
  change 39*columns n L+12+RamShortExtraction.cost n L (H*D)≤39*S+12+RamShortExtractionBounds.time S r
  have hh:=Nat.mul_le_mul_left 39 hcS
  omega

end Lax455465Proofs.RamShortFinish
