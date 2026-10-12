import Lax455465Proofs.RamAllCommodities
import Lax455465Proofs.RamShortEmit
import Lax455465Proofs.LayeredExtractionCertificate

set_option maxRecDepth 16384
namespace Lax455465Proofs.RamShortExtraction
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamRational
open LayeredFlowLP LayeredGraphFlow LayeredWalkState LayeredPathSweep
open Lax455465.RationalEncoding PathRecordBuffer RamExtractionStep RamExtractionData
open scoped NNRat NNReal

def readValue : Com := .seq (.assign "short.valueIndex" (.lit 0))
  (RamUnsignedBuffer.read "flow.primal" "short.valueIndex")

def command : Com := .seq readValue (.seq RamShortHeader.command
  (.seq RamAllCommodities.command RamShortEmit.command))

def outputLength (n L : ℕ) : ℕ := 3+n*n*LayeredCommodityState.budget n L*(L+4)
def reserve (n L : ℕ) : ℕ := 3+(n*n+1)*LayeredCommodityState.budget n L*(L+4)+L+5
def cost (n L M : ℕ) : ℕ := 16+36*(2*M).size+53+
  ((RamAllCommodities.innerCost n L M+26)*(n*n)+6)+13*outputLength n L+11

theorem read_spec (B : ℕ) {n L : ℕ} (q : Coordinate n L → ℚ≥0) (hB : 3<B)
    (hn : (q 0).num<B) (hd : (q 0).den<B) :
    Spec B (Data q) readValue
      (fun _ τ => Data q τ ∧ FractionOutput (q 0 : ℚ) τ ∧ τ.vars "rat.s"=0) 16 := by
  intro σ hσ
  let ν:=σ.setVar "short.valueIndex" 0
  have r1 : Run B (.assign "short.valueIndex" (.lit 0)) σ ν 2 := Run.assign (evalB_lit (by omega))
  have hq : (List.ofFn q)[0]'(by simp) = q 0 := by simp
  obtain ⟨τ,r2,p2⟩ := RamUnsignedBuffer.read_spec B "flow.primal" "short.valueIndex" (List.ofFn q) 0
    (by simp) (by omega) (by omega) (by simpa only [hq] using hn) (by simpa only [hq] using hd) (by decide) ν
    ⟨by simpa only [Prefix,ν,arrs_setVar] using hσ.buffer,by simp [ν]⟩
  exact ⟨τ,r1.seq r2,frame (r1.seq r2) hσ (by decide) (by decide),by simpa only [hq] using p2⟩

theorem encoded_length {n : ℕ} (f : ℚ≥0) (rs : PathRecordBuffer.Records n) :
    (encodeFlow ⟨f,rs⟩).length=3+(encode rs).length := by
  simp [encodeFlow,encode,RamPathRecord.encode,RamPathState.simple,encodeRational]
  omega

/-- The entire fixed native extraction starts from a decoded primal buffer,
and writes an exact path certificate satisfying the public flow semantics. -/
theorem command_spec (B D H : ℕ) {n L : ℕ} (I : RationalInstance n)
    (q₀ : Coordinate n L → ℚ≥0) (hn : 0<n) (hL : 1≤L) (hD : 0<D) (hH : 1≤H)
    (hB : 2*(H*D)^2+3<B)
    (hsize : n+n*n+L*(n*n)+2*(1+(n*n)*(L*(n*n)))+2*L+20<B)
    (hreserve : reserve n L<B) (hcount : (n*n+1)*LayeredCommodityState.budget n L+1<B)
    (hq : ∀ j,ResidualLattice.Bounded D H (q₀ j)) (ha : ResidualLattice.Bounded D H (q₀ 0/2))
    (hf : LayeredFlowFeasibility.Feasible I (q₀ 0 : ℚ) (arc q₀)) :
    Spec B (fun σ => Data q₀ σ ∧ reserve n L<(σ.arrs "short.output").length ∧ σ.out=[]) command
      (fun _ τ => ∃ q rs,LayeredExtractionState.State q₀ (q₀ 0/2) D H (n*n) q rs ∧
        τ.out=encodeFlow ⟨q₀ 0,rs⟩ ∧
        Lax455465.ConcurrentFlow.IsConcurrentFlow .undirected I.network
          (Lax455465.ProductNetwork.uniformWeight n) (q₀ 0 : ℝ≥0) (FlowCertificate.flow ⟨q₀ 0,rs⟩) ∧
        Lax455465.ShortPathFlow.HasPathLengthAtMost (FlowCertificate.flow ⟨q₀ 0,rs⟩) (L : ℝ))
      (cost n L (H*D)) := by
  let M:=H*D
  have hMB : M<B := by dsimp only [M]; nlinarith only [hB]
  have h2M : 2*M<B := by dsimp only [M]; nlinarith only [hB]
  have hheight := ResidualLattice.height (hq 0) hD hH
  have hnum : (q₀ 0).num<B := by simpa only [NNRat.natAbs_num_coe] using hheight.1.trans_lt hMB
  have hden : (q₀ 0).den<B := hheight.2.trans_lt hMB
  rintro σ ⟨hd,hroom,hout⟩
  obtain ⟨s1,r1,p1⟩ := read_spec B q₀ (by omega) hnum hden σ hd
  obtain ⟨s2,r2,p2⟩ := RamShortHeader.command_spec B M (q₀ 0) (by omega) h2M hheight s1
    ⟨p1.2.1,p1.2.2,by rw [RamFrames.run_array_length r1 "short.output"]; dsimp only [reserve] at hroom; omega⟩
  have hd2 := frame r2 p1.1 (by decide) (by decide)
  have hb (st : Edge n) (hst : st.1≠st.2) :
      AcyclicFlowPath.Balance (graph (arc q₀) st) (0,st.1) (Fin.last L,st.2) ((q₀ 0/2 : ℚ≥0) : ℚ) := by
    simpa using LayeredGraphFlow.balance I (q₀ 0 : ℚ) (arc q₀) hf st.1 st.2 hst
  have hinit : RamAllCommodities.Context q₀ (q₀ 0/2) D H (RamShortHeader.header (q₀ 0)) 0 0 s2 := by
    refine ⟨Nat.zero_le _,p2.2.1,?_,q₀,[],LayeredExtractionState.initial q₀ (q₀ 0/2) D H hq hb,hd2,?_⟩
    · rw [RamFrames.run_array_length r2 "short.output",RamFrames.run_array_length r1 "short.output"]
      dsimp only [RamShortHeader.header,encodeRational,reserve] at *
      simp only [List.length_append,List.length_cons,List.length_nil]
      omega
    · simpa only [encode,List.flatMap_nil,List.append_nil,List.length_nil,Nat.zero_add] using p2.1
  obtain ⟨s3,r3,q,rs,hm,hd3,ho3⟩ := RamAllCommodities.command_spec B D H q₀ (q₀ 0/2)
    (RamShortHeader.header (q₀ 0)) 0 hn hL hD hH hB hsize
    (by dsimp only [RamShortHeader.header,encodeRational,reserve] at hreserve ⊢;
        simp only [List.length_append,List.length_cons,List.length_nil]; exact hreserve)
    (by simpa only [Nat.zero_add] using hcount) ha s2 hinit
  have hlen : (encodeFlow ⟨q₀ 0,rs⟩).length≤outputLength n L := by
    rw [encoded_length]
    have hh:=length_bound rs (fun r hr => (hm.good r hr).2.2.2)
    have hc:=Nat.mul_le_mul_right (L+4) hm.count
    dsimp only [outputLength]
    omega
  have hwords : ∀ x∈encodeFlow ⟨q₀ 0,rs⟩,x<B := by
    intro x hx
    simp only [encodeFlow,encodeRational,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with ((rfl | rfl) | rfl) | hx
    · exact hnum
    · exact hden
    · have hh:=hm.count
      have hp := Nat.mul_le_mul_left (n*n+1) (show 1≤LayeredCommodityState.budget n L by simp [LayeredCommodityState.budget])
      nlinarith only [hh,hcount,hp]
    · obtain ⟨r,hr,hx⟩:=List.mem_flatMap.mp hx
      simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with (rfl | hx) | (rfl | rfl)
      · exact (hm.good r hr).2.2.2.trans_lt (by omega)
      · obtain ⟨v,hv,rfl⟩:=List.mem_map.mp hx
        exact v.isLt.trans (by omega)
      · have hh:=(ResidualLattice.height (hm.weights r hr) hD hH).1
        simpa only [NNRat.natAbs_num_coe] using hh.trans_lt hMB
      · exact (ResidualLattice.height (hm.weights r hr) hD hH).2.trans_lt hMB
  have hlenB : (encodeFlow ⟨q₀ 0,rs⟩).length<B := hlen.trans_lt (by
    have hp:=Nat.mul_le_mul_left (LayeredCommodityState.budget n L*(L+4)) (Nat.le_succ (n*n))
    dsimp only [outputLength,reserve] at *
    nlinarith only [hp,hreserve])
  obtain ⟨τ,r4,p4⟩ := RamShortEmit.command_spec B (q₀ 0) rs (by omega) hlenB hwords s3
    ⟨by simpa only [Nat.zero_add] using ho3,(r1.seq (r2.seq r3)).out_eq (by decide) |>.trans hout⟩
  have hcorrect:=LayeredExtractionCertificate.correct I (q₀ 0) q₀ q D H rs hm hf
  refine ⟨τ,(r1.seq (r2.seq (r3.seq r4))).mono ?_,q,rs,hm,p4,hcorrect⟩
  dsimp only [cost,M]
  have hh:=Nat.mul_le_mul_left 13 hlen
  omega

end Lax455465Proofs.RamShortExtraction
