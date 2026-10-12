import Lax455465Proofs.RamArrayReplace
import Lax455465Proofs.RamTruncatedSubtract
import Lax455465Proofs.RamUnsignedScalar

namespace Lax455465Proofs.RamResidualUpdate
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamRational UnsignedArray
open scoped NNRat

/-- Subtract the selected path amount from the runtime residual coordinate
and store its exact canonical numerator and denominator back in place. -/
def command : Com := .seq (RamUnsignedBuffer.read "flow.primal" "short.arcIndex")
  (.seq (RamUnsignedArithmetic.copy "left")
  (.seq (RamUnsignedScalar.load "short.amount")
  (.seq (RamUnsignedArithmetic.copy "right")
  (.seq RamTruncatedSubtract.command (RamArrayReplace.command "flow.primal" "short.arcIndex")))))

theorem command_spec (B M : ℕ) {N : ℕ} (q : Fin N → ℚ≥0) (j : Fin N) (w : ℚ≥0)
    (hB : 2*M^2+3<B) (hindex : 2*N+1<B)
    (hjn : (q j).num≤M) (hjd : (q j).den≤M) (hwn : w.num≤M) (hwd : w.den≤M)
    (hrn : (RamTruncatedSubtract.value (q j) w).num<B)
    (hrd : (RamTruncatedSubtract.value (q j) w).den<B) :
    Spec B (fun σ => Initialized q "flow.primal" σ ∧ σ.vars "short.arcIndex"=j.val ∧
      RamUnsignedScalar.Stored "short.amount" w σ) command
      (fun _ τ => Initialized (Function.update q j (RamTruncatedSubtract.value (q j) w)) "flow.primal" τ)
      (36*(M^2).size+200) := by
  have hMB : M<B := by nlinarith only [hB]
  have h1 : 1<B := by omega
  have h2 : 2<B := by omega
  rintro σ ⟨hbuf,hj,hw⟩
  obtain ⟨s1,r1,p1⟩ := RamUnsignedBuffer.read_spec B "flow.primal" "short.arcIndex" (List.ofFn q) j.val
    (by simpa only [List.length_ofFn] using j.isLt) h2 (by omega)
    (by simpa only [List.getElem_ofFn,Fin.eta] using hjn.trans_lt hMB)
    (by simpa only [List.getElem_ofFn,Fin.eta] using hjd.trans_lt hMB) (by decide) σ
    ⟨to_prefix q _ σ hbuf,hj⟩
  have hq1 : FractionOutput (q j : ℚ) s1 := by simpa only [List.getElem_ofFn,Fin.eta] using p1.1
  obtain ⟨s2,r2,p2⟩ := RamUnsignedArithmetic.copy_spec B (q j) "left" h1
    (hjn.trans_lt hMB) (hjd.trans_lt hMB) (by decide) s1 hq1
  have hw2 : RamUnsignedScalar.Stored "short.amount" w s2 := by
    simpa only [RamUnsignedScalar.Stored,String.reduceAppend,(r1.seq r2).frame_var "short.amount.n" (by decide),
      (r1.seq r2).frame_var "short.amount.d" (by decide)] using hw
  obtain ⟨s3,r3,p3⟩ := RamUnsignedScalar.load_spec B "short.amount" w h1
    (hwn.trans_lt hMB) (hwd.trans_lt hMB) (by decide) s2 hw2
  obtain ⟨s4,r4,p4⟩ := RamUnsignedArithmetic.copy_spec B w "right" h1
    (hwn.trans_lt hMB) (hwd.trans_lt hMB) (by decide) s3 p3
  have hleft : s4.vars "left.s"=0 ∧ s4.vars "left.n"=(q j).num ∧ s4.vars "left.d"=(q j).den := by
    simpa only [String.reduceAppend,(r3.seq r4).frame_var "left.s" (by decide),
      (r3.seq r4).frame_var "left.n" (by decide),(r3.seq r4).frame_var "left.d" (by decide)] using p2
  obtain ⟨s5,r5,p5⟩ := RamTruncatedSubtract.command_spec B M (q j) w hB hjn hjd hwn hwd s4
    ⟨hleft.1,hleft.2.1,hleft.2.2,p4⟩
  have before := r1.seq (r2.seq (r3.seq (r4.seq r5)))
  have hq5 : Initialized q "flow.primal" s5 := by
    simpa only [Initialized,before.frame_arr "flow.primal" (by decide)] using hbuf
  have hj5 := (before.frame_var "short.arcIndex" (by decide)).trans hj
  obtain ⟨τ,r6,p6⟩ := RamArrayReplace.command_spec B q j (RamTruncatedSubtract.value (q j) w)
    "flow.primal" "short.arcIndex" hindex hrn hrd s5 ⟨hq5,hj5,p5⟩
  have hs : ((q j).den*w.den).size≤(M^2).size := Nat.size_le_size (by nlinarith [Nat.mul_le_mul hjd hwd])
  exact ⟨τ,(r1.seq (r2.seq (r3.seq (r4.seq (r5.seq r6))))).mono (by omega),p6⟩

end Lax455465Proofs.RamResidualUpdate
