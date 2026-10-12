import Lax455465Proofs.RamShortPrepare
import Lax455465Proofs.RamShortFinish
import Lax455465Proofs.ShortSelectedBounds
import Lax455465Proofs.RamInputFlowLp
import Lax455465Proofs.RamShortNoWrite

set_option maxRecDepth 16384
namespace Lax455465Proofs.RamShortValidInput
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState
open Lax455465.RationalEncoding Lax455465.ProductNetwork Lax455465.ConcurrentFlow Lax455465.ShortPathFlow
open Lax759944.BinaryWordEncoding
open scoped NNRat NNReal

structure Input {n : ℕ} (I : RationalInstance n) (TB : Polynomial ℕ) (σ : Env) : Prop where
  tape : σ.inp=(encodeInput .undirected I).length::encodeInput .undirected I
  copied : (encodeInput .undirected I).length≤(σ.arrs "input.data").length
  weights : 2*n<(σ.arrs "flow.weights").length
  capacities : 2*(n*n)<(σ.arrs "flow.capacities").length
  lp : LayeredLpSize.sizeBound.eval (bitSize (encodeInput .undirected I))<(σ.arrs "lp.word").length
  vmInput : LayeredLpSize.sizeBound.eval (bitSize (encodeInput .undirected I))<(σ.arrs "vm.input").length
  addresses : TB.eval (LayeredLpSize.sizeBound.eval (bitSize (encodeInput .undirected I)))<(σ.arrs "vm.addresses").length
  values : TB.eval (LayeredLpSize.sizeBound.eval (bitSize (encodeInput .undirected I)))<(σ.arrs "vm.values").length
  vmOutput : TB.eval (LayeredLpSize.sizeBound.eval (bitSize (encodeInput .undirected I)))<(σ.arrs "vm.output").length
  primal : 2*LayeredLpSize.sizeBound.eval (bitSize (encodeInput .undirected I))<(σ.arrs "flow.primal").length
  raw : LayeredLpSize.sizeBound.eval (bitSize (encodeInput .undirected I))+1<(σ.arrs "short.raw").length
  simple : LayeredLpSize.sizeBound.eval (bitSize (encodeInput .undirected I))+1<(σ.arrs "short.simple").length
  output : RamShortExtractionBounds.space (LayeredLpSize.sizeBound.eval (bitSize (encodeInput .undirected I)))<(σ.arrs "short.output").length
  empty : σ.out=[]

/-- Read the original physical tape, solve the selected layered LP, and
emit the matching short-path certificate with polynomial resources. -/
theorem exists_program : ∃ (c : Com) (T WB sourceTime : Polynomial ℕ),
    ∀ {n : ℕ} (I : RationalInstance n),I.network.IsUndirected → (∀ v,I.weight v=1) → 2≤n →
      0<sparsestCut I.network (uniformWeight n) →
      ∀ W : ℕ,WB.eval (bitSize (encodeInput .undirected I))≤W →
        Spec (2^W) (Input I sourceTime) c (fun _ τ => ∃ cert : FlowCertificate n,
          τ.out=encodeFlow cert ∧ IsConcurrentFlow .undirected I.network (uniformWeight n) (cert.value : ℝ≥0) cert.flow ∧
          (sparsestCut I.network (uniformWeight n) : ℝ)≤32768*logFactor n*(cert.value : ℝ) ∧
          HasPathLengthAtMost cert.flow (8192*(maxIncidentCapacity I.network : ℝ)*logFactor n /
            ((n : ℝ)*(sparsestCut I.network (uniformWeight n) : ℝ))))
          (T.eval (bitSize (encodeInput .undirected I))) := by
  obtain ⟨p,sourceWord,sourceTime,coefficients,hprepare⟩:=RamShortPrepare.exists_program
  let c : Com:=.seq RamInputCopy.copy (.seq RamGraphInput.command
    (.seq (RamShortPrepare.command p coefficients) RamShortFinish.command))
  let parsing : Polynomial ℕ:=Polynomial.C 200*(Polynomial.X+Polynomial.C 1)^2
  let WB:=RamShortScan.wordBound p sourceWord sourceTime+RamShortFinish.wordBound sourceWord+
    LpInputSize.sizeBound+Polynomial.X+Polynomial.C 10
  refine ⟨c,RamShortPrepare.timeBound p coefficients sourceTime+RamShortFinish.timeBound sourceWord+parsing,WB,sourceTime,?_⟩
  intro n I hsym hw hn hS W hW
  let b:=bitSize (encodeInput .undirected I)
  let oldS:=LpInputSize.sizeBound.eval b
  let S:=LayeredLpSize.sizeBound.eval b
  have hsum : (RamShortScan.wordBound p sourceWord sourceTime).eval b+
      (RamShortFinish.wordBound sourceWord).eval b+oldS+b+10≤W := by
    simpa only [WB,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_C,b,oldS] using hW
  have hB : W<2^W:=Nat.lt_two_pow_self
  have hscanW : (RamShortScan.wordBound p sourceWord sourceTime).eval (bitSize (encodeInput .undirected I))≤W := by
    change (RamShortScan.wordBound p sourceWord sourceTime).eval b≤W
    omega
  have hfinishW : (RamShortFinish.wordBound sourceWord).eval (bitSize (encodeInput .undirected I))≤W := by
    change (RamShortFinish.wordBound sourceWord).eval b≤W
    omega
  have hlenb : (encodeInput .undirected I).length≤b:=WordSize.length_le _
  have hLPword : RamFlowLp.wordLength n≤oldS := by
    rw [←FlowEncodingSizes.flow_length I]
    exact (WordSize.length_le _).trans (LpInputSize.flow_program_polynomial_size .undirected I)
  have hr : RamFlowData.rows n<2^W := by dsimp only [RamFlowLp.wordLength] at hLPword; omega
  have hc : RamFlowData.columns n<2^W := by dsimp only [RamFlowLp.wordLength] at hLPword; omega
  have hm : RamFlowData.rows n*RamFlowData.columns n<2^W := by dsimp only [RamFlowLp.wordLength] at hLPword; omega
  have hn2 : n*n<2^W := by dsimp only [RamFlowData.rows] at hr; omega
  have hn3 : (n*n)*n<2^W := by dsimp only [RamFlowData.rows] at hr; omega
  have hnB : n<2^W := by rw [RamInputFlowLp.input_length] at hlenb; omega
  have hwords : ∀ a∈encodeInput .undirected I,a<2^W := by
    intro a ha
    exact (WordSize.member_bound _ a ha).trans_le (Nat.pow_le_pow_right (by decide) (by omega : b≤W))
  have hwsize (v : Fin n) : (I.weight v).den.size≤b := by
    have hh:=WordSize.member_size _ _ (LpInputSize.weight_members .undirected I v (I.weight v).den (by simp [encodeRational]))
    omega
  have hcsize (u v : Fin n) : (I.capacity u v).den.size≤b := by
    have hh:=WordSize.member_size _ _ (LpInputSize.capacity_members .undirected I u v (I.capacity u v).den (by simp [encodeRational]))
    omega
  obtain ⟨f,x,y,hmath,hfit,hrun⟩:=hprepare .undirected I hn
  obtain ⟨hmin,hmax,hvalue,hlength⟩:=ShortSelectedBounds.guarantees I hsym hw hn hS f x y
    (fun L => (hmath L).1) (fun L => (hmath L).2.1) (fun L => (hmath L).2.2)
  let L:=ShortLayerSelection.select n (ShortRationalParameters.maximum I : ℚ) (fun k => (f k : ℚ))
  change 1≤L at hmin
  change L≤n-1 at hmax
  rintro σ hσ
  obtain ⟨s1,r1,p1⟩:=RamInputCopy.copy_spec (2^W) (encodeInput .undirected I) (by omega)
    (by omega) hwords σ ⟨hσ.tape,hσ.copied⟩
  obtain ⟨s2,r2,p2⟩:=RamGraphInput.command_spec (2^W) b .undirected I (by omega) hnB hn2 hn3 hr hc hm
    (by omega) hwords hwsize hcsize s1
    ⟨p1.2.2,by simpa only [RamFrames.run_array_length r1 "flow.weights"] using hσ.weights,
      by simpa only [RamFrames.run_array_length r1 "flow.capacities"] using hσ.capacities⟩
  have r12:=r1.seq r2
  have hpinput : RamShortPrepare.Input I S (sourceTime.eval S) s2 := by
    refine ⟨⟨p2.1.1,p2.1.2.1,p2.1.2.2.2.2.2.2.2⟩,?_,?_,?_,?_,?_⟩
    · simpa only [RamFrames.run_array_length r12 "lp.word"] using hσ.lp
    · simpa only [RamFrames.run_array_length r12 "vm.input"] using hσ.vmInput
    · simpa only [RamFrames.run_array_length r12 "vm.addresses"] using hσ.addresses
    · simpa only [RamFrames.run_array_length r12 "vm.values"] using hσ.values
    · simpa only [RamFrames.run_array_length r12 "vm.output"] using hσ.vmOutput
  obtain ⟨s3,r3,p3⟩:=hrun W hscanW s2 hpinput
  have r123:=r1.seq (r2.seq r3)
  obtain ⟨τ,r4,rs,he,hflow,hlen⟩:=RamShortFinish.command_spec sourceWord I L (f L) (x L) (y L) hn hmin
    (by omega) (hmath L).1 (hfit L) W hfinishW s3
    ⟨p3.2.1,p3.2.2,
      by simpa only [RamFrames.run_array_length r123 "flow.primal"] using hσ.primal,
      by simpa only [RamFrames.run_array_length r123 "short.raw"] using hσ.raw,
      by simpa only [RamFrames.run_array_length r123 "short.simple"] using hσ.simple,
      by simpa only [RamFrames.run_array_length r123 "short.output"] using hσ.output,
      (r123.out_eq ⟨by decide,by decide,RamShortNoWrite.prepare p coefficients⟩).trans hσ.empty⟩
  have hcount : n+n*n≤b := by rw [RamInputFlowLp.input_length] at hlenb; omega
  have hparse : 12*(encodeInput .undirected I).length+7+((36*b+56)*(n+n*n)+52)≤parsing.eval b := by
    have hp:=Nat.mul_le_mul_left (36*b+56) hcount
    simp only [parsing,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_add,Polynomial.eval_X]
    nlinarith only [hp,hlenb]
  refine ⟨τ,(r1.seq (r2.seq (r3.seq r4))).mono ?_,⟨f L,rs⟩,he,hflow,hvalue,?_⟩
  · simp only [Polynomial.eval_add]
    dsimp only [b] at hparse ⊢
    omega
  · intro path hp
    exact (hlen path hp).trans hlength

end Lax455465Proofs.RamShortValidInput
