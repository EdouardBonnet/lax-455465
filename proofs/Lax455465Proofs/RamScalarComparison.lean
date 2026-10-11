import Lax455465Proofs.RamUnsignedScalar
import Lax455465Proofs.RamComparison

namespace Lax455465Proofs.RamScalarComparison

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamUnsignedScalar
open scoped NNRat

def command (leftName rightName : String) : Com := .seq (load leftName)
  (.seq (RamUnsignedArithmetic.copy "left") (.seq (load rightName)
    (.seq (RamUnsignedArithmetic.copy "right") RamComparison.compareFraction)))

/-- Compare two stored exact nonnegative rationals without losing equality
at radius events or mass ties. The result is a canonical zero/one word. -/
theorem command_spec (B M : ℕ) (a b : ℚ≥0) (leftName rightName : String)
    (hB : 2*M^2+3 < B) (han : a.num ≤ M) (had : a.den ≤ M) (hbn : b.num ≤ M) (hbd : b.den ≤ M)
    (hlfresh : leftName ++ ".n" ≠ "rat.s" ∧ leftName ++ ".d" ≠ "rat.s" ∧ leftName ++ ".d" ≠ "rat.n")
    (hrfresh : rightName ++ ".n" ≠ "rat.s" ∧ rightName ++ ".d" ≠ "rat.s" ∧ rightName ++ ".d" ≠ "rat.n")
    (hrretain : rightName ++ ".n" ∉ (Com.seq (load leftName) (RamUnsignedArithmetic.copy "left")).wvars ∧
      rightName ++ ".d" ∉ (Com.seq (load leftName) (RamUnsignedArithmetic.copy "left")).wvars) :
    Spec B (fun σ => Stored leftName a σ ∧ Stored rightName b σ)
      (command leftName rightName) (fun _ τ => τ.vars "cmp.le" = if (a : ℚ) ≤ (b : ℚ) then 1 else 0) 64 := by
  have hM : M < B := by nlinarith
  have h1 : 1 < B := by nlinarith
  rintro σ ⟨ha,hb⟩
  obtain ⟨ν,ra,pa⟩ := load_spec B leftName a h1 (han.trans_lt hM) (had.trans_lt hM) hlfresh σ ha
  obtain ⟨μ,rl,pl⟩ := RamUnsignedArithmetic.copy_spec B a "left" h1 (han.trans_lt hM) (had.trans_lt hM) (by decide) ν pa
  have hbμ : Stored rightName b μ := by
    have rr := ra.seq rl
    simpa only [Stored,rr.frame_var (rightName ++ ".n") hrretain.1,rr.frame_var (rightName ++ ".d") hrretain.2] using hb
  obtain ⟨ξ,rb,pb⟩ := load_spec B rightName b h1 (hbn.trans_lt hM) (hbd.trans_lt hM) hrfresh μ hbμ
  obtain ⟨η,rr,pr⟩ := RamUnsignedArithmetic.copy_spec B b "right" h1 (hbn.trans_lt hM) (hbd.trans_lt hM) (by decide) ξ pb
  have plη : η.vars "left.s"=0 ∧ η.vars "left.n"=a.num ∧ η.vars "left.d"=a.den := by
    have r := rb.seq rr
    simpa only [r.frame_var "left.s" (by simp [load,RamUnsignedArithmetic.copy,Com.wvars]),
      r.frame_var "left.n" (by simp [load,RamUnsignedArithmetic.copy,Com.wvars]),r.frame_var "left.d" (by simp [load,RamUnsignedArithmetic.copy,Com.wvars]),String.reduceAppend] using pl
  obtain ⟨τ,rc,pc⟩ := RamComparison.compareFraction_spec B M 0 a.num a.den 0 b.num b.den hB
    (by omega) (by omega) han had hbn hbd a.den_pos b.den_pos η
    ⟨plη.1,plη.2.1,plη.2.2,by simpa only [String.reduceAppend] using pr⟩
  refine ⟨τ,ra.seq (rl.seq (rb.seq (rr.seq rc))),?_⟩
  have hp : τ.vars "cmp.le"=1 ↔ (a : ℚ)≤(b : ℚ) := by simpa only [RamUnsignedArithmetic.value] using pc.2
  by_cases h : (a : ℚ)≤(b : ℚ)
  · simpa only [if_pos h] using hp.mpr h
  · have hz : τ.vars "cmp.le"=0 := by have hn := mt hp.mp h; omega
    simpa only [if_neg h] using hz

end Lax455465Proofs.RamScalarComparison
