import Lax455465Proofs.RamUnsignedScalar
import Lax455465Proofs.RamMinimum

namespace Lax455465Proofs.RamScalarBinary

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamUnsignedScalar
open scoped NNRat

def command (leftName rightName : String) (operation : Com) : Com :=
  .seq (load leftName) (.seq (RamUnsignedArithmetic.copy "left")
    (.seq (load rightName) (.seq (RamUnsignedArithmetic.copy "right") operation)))

/-- Pass two persistent canonical rational pairs to a fixed native arithmetic
operation. The command loads runtime registers and retains the operation's
exact execution guarantee. -/
theorem command_spec (B M K : ℕ) (a b : ℚ≥0) (leftName rightName : String)
    (operation : Com) (q : ℚ) (hB : 2*M^2+3 < B)
    (han : a.num ≤ M) (had : a.den ≤ M) (hbn : b.num ≤ M) (hbd : b.den ≤ M)
    (hlfresh : leftName ++ ".n" ≠ "rat.s" ∧ leftName ++ ".d" ≠ "rat.s" ∧ leftName ++ ".d" ≠ "rat.n")
    (hrfresh : rightName ++ ".n" ≠ "rat.s" ∧ rightName ++ ".d" ≠ "rat.s" ∧ rightName ++ ".d" ≠ "rat.n")
    (hrretain : rightName ++ ".n" ∉ (Com.seq (load leftName) (RamUnsignedArithmetic.copy "left")).wvars ∧
      rightName ++ ".d" ∉ (Com.seq (load leftName) (RamUnsignedArithmetic.copy "left")).wvars)
    (hop : Spec B (fractionInputs 0 a.num a.den 0 b.num b.den) operation
      (fun _ τ => FractionOutput q τ) K) :
    Spec B (fun σ => Stored leftName a σ ∧ Stored rightName b σ)
      (command leftName rightName operation) (fun _ τ => FractionOutput q τ) (K+24) := by
  have hM : M < B := by nlinarith
  have h1 : 1 < B := by nlinarith
  rintro σ ⟨ha,hb⟩
  obtain ⟨ν,ra,pa⟩ := load_spec B leftName a h1 (han.trans_lt hM) (had.trans_lt hM) hlfresh σ ha
  obtain ⟨μ,rleft,pleft⟩ := RamUnsignedArithmetic.copy_spec B a "left" h1
    (han.trans_lt hM) (had.trans_lt hM) (by decide) ν pa
  have hbμ : Stored rightName b μ := by
    have rr := ra.seq rleft
    simpa only [Stored,rr.frame_var (rightName ++ ".n") hrretain.1,
      rr.frame_var (rightName ++ ".d") hrretain.2] using hb
  obtain ⟨ξ,rb,pb⟩ := load_spec B rightName b h1 (hbn.trans_lt hM) (hbd.trans_lt hM) hrfresh μ hbμ
  obtain ⟨η,rright,pright⟩ := RamUnsignedArithmetic.copy_spec B b "right" h1
    (hbn.trans_lt hM) (hbd.trans_lt hM) (by decide) ξ pb
  have pleftη : η.vars "left.s" = 0 ∧ η.vars "left.n" = a.num ∧ η.vars "left.d" = a.den := by
    have rr := rb.seq rright
    simpa only [rr.frame_var "left.s" (by simp [load,RamUnsignedArithmetic.copy,Com.wvars]),rr.frame_var "left.n" (by simp [load,RamUnsignedArithmetic.copy,Com.wvars]),
      rr.frame_var "left.d" (by simp [load,RamUnsignedArithmetic.copy,Com.wvars]),String.reduceAppend] using pleft
  obtain ⟨τ,rop,pop⟩ := hop η ⟨pleftη.1,pleftη.2.1,pleftη.2.2,by simpa only [String.reduceAppend] using pright⟩
  refine ⟨τ,(ra.seq (rleft.seq (rb.seq (rright.seq rop)))).mono (by omega),pop⟩

end Lax455465Proofs.RamScalarBinary
