import Lax455465Proofs.RamTruncatedSubtract
import Lax455465Proofs.RamUnsignedScalar

namespace Lax455465Proofs.RamRemainingSubtract
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational
open scoped NNRat

def command : Com := .seq (RamUnsignedScalar.load "short.remaining")
  (.seq (RamUnsignedArithmetic.copy "left")
  (.seq (RamUnsignedScalar.load "short.amount")
  (.seq (RamUnsignedArithmetic.copy "right")
  (.seq RamTruncatedSubtract.command (RamUnsignedScalar.save "short.remaining")))))

/-- Reduce the exact remaining commodity demand by the emitted path
amount. A final bottleneck equal to the remainder produces canonical zero. -/
theorem command_spec (B M : ℕ) (a w : ℚ≥0) (hB : 2*M^2+3<B)
    (han : a.num≤M) (had : a.den≤M) (hwn : w.num≤M) (hwd : w.den≤M)
    (hrn : (RamTruncatedSubtract.value a w).num<B) (hrd : (RamTruncatedSubtract.value a w).den<B) :
    Spec B (fun σ => RamUnsignedScalar.Stored "short.remaining" a σ ∧ RamUnsignedScalar.Stored "short.amount" w σ)
      command (fun _ τ => RamUnsignedScalar.Stored "short.remaining" (RamTruncatedSubtract.value a w) τ)
      (36*(M^2).size+180) := by
  have hMB : M<B := by nlinarith only [hB]
  have h1 : 1<B := by omega
  rintro σ ⟨ha,hw⟩
  obtain ⟨s1,r1,p1⟩ := RamUnsignedScalar.load_spec B "short.remaining" a h1
    (han.trans_lt hMB) (had.trans_lt hMB) (by decide) σ ha
  obtain ⟨s2,r2,p2⟩ := RamUnsignedArithmetic.copy_spec B a "left" h1
    (han.trans_lt hMB) (had.trans_lt hMB) (by decide) s1 p1
  have hw2 : RamUnsignedScalar.Stored "short.amount" w s2 := by
    simpa only [RamUnsignedScalar.Stored,String.reduceAppend,(r1.seq r2).frame_var "short.amount.n" (by decide),
      (r1.seq r2).frame_var "short.amount.d" (by decide)] using hw
  obtain ⟨s3,r3,p3⟩ := RamUnsignedScalar.load_spec B "short.amount" w h1
    (hwn.trans_lt hMB) (hwd.trans_lt hMB) (by decide) s2 hw2
  obtain ⟨s4,r4,p4⟩ := RamUnsignedArithmetic.copy_spec B w "right" h1
    (hwn.trans_lt hMB) (hwd.trans_lt hMB) (by decide) s3 p3
  have hleft : s4.vars "left.s"=0 ∧ s4.vars "left.n"=a.num ∧ s4.vars "left.d"=a.den := by
    simpa only [String.reduceAppend,(r3.seq r4).frame_var "left.s" (by decide),
      (r3.seq r4).frame_var "left.n" (by decide),(r3.seq r4).frame_var "left.d" (by decide)] using p2
  obtain ⟨s5,r5,p5⟩ := RamTruncatedSubtract.command_spec B M a w hB han had hwn hwd s4
    ⟨hleft.1,hleft.2.1,hleft.2.2,p4⟩
  obtain ⟨τ,r6,p6⟩ := RamUnsignedScalar.save_spec B "short.remaining" (RamTruncatedSubtract.value a w) hrn hrd (by decide) s5 p5
  have hs : (a.den*w.den).size≤(M^2).size := Nat.size_le_size (by nlinarith [Nat.mul_le_mul had hwd])
  exact ⟨τ,(r1.seq (r2.seq (r3.seq (r4.seq (r5.seq r6))))).mono (by omega),p6⟩

end Lax455465Proofs.RamRemainingSubtract
