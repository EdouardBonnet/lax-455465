import Lax455465Proofs.RamScalarBinary
import Lax455465Proofs.RamTruncatedSubtract
import Lax455465Proofs.RamRegionContext

namespace Lax455465Proofs.RamScalarDifference
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamUnsignedScalar RamRegionContext
open scoped NNRat

def command (leftName rightName target : String) : Com :=
  .seq (RamScalarBinary.command leftName rightName RamTruncatedSubtract.command) (save target)

theorem value_eq (a b : ℚ≥0) : RamTruncatedSubtract.value a b=a-b := by
  apply NNRat.coe_injective
  by_cases h : b≤a
  · rw [NNRat.coe_sub h]
    simp only [RamTruncatedSubtract.value,NNRat.coe_mk,max_eq_left (sub_nonneg.mpr (NNRat.coe_le_coe.mpr h))]
  · rw [tsub_eq_zero_of_le (le_of_not_ge h)]
    simp only [RamTruncatedSubtract.value,NNRat.coe_mk,NNRat.coe_zero,max_eq_right (sub_nonpos.mpr (NNRat.coe_le_coe.mpr (le_of_not_ge h)))]

/-- Subtract stored nonnegative rationals with canonical clipping at zero,
and save the exact result in a persistent register pair. -/
theorem command_spec (B M : ℕ) (a b : ℚ≥0) (leftName rightName target : String)
    (hB : 2*M^2+3<B) (ha : LpInputSize.Height M (a : ℚ)) (hb : LpInputSize.Height M (b : ℚ))
    (hout : LpInputSize.Height M ((a-b : ℚ≥0) : ℚ))
    (hlfresh : leftName++".n"≠"rat.s" ∧ leftName++".d"≠"rat.s" ∧ leftName++".d"≠"rat.n")
    (hrfresh : rightName++".n"≠"rat.s" ∧ rightName++".d"≠"rat.s" ∧ rightName++".d"≠"rat.n")
    (hrretain : rightName++".n"∉(Com.seq (load leftName) (RamUnsignedArithmetic.copy "left")).wvars ∧
      rightName++".d"∉(Com.seq (load leftName) (RamUnsignedArithmetic.copy "left")).wvars)
    (htarget : target++".n"≠"rat.d") :
    Spec B (fun σ => Stored leftName a σ ∧ Stored rightName b σ) (command leftName rightName target)
      (fun _ τ => Stored target (a-b) τ) (36*(a.den*b.den).size+170) := by
  have hMB : M<B := by nlinarith
  have hop := RamTruncatedSubtract.command_spec B M a b hB (num_bound ha) (den_bound ha) (num_bound hb) (den_bound hb)
  rintro σ hσ
  obtain ⟨ν,rr,pr⟩ := RamScalarBinary.command_spec B M (36*(a.den*b.den).size+142) a b leftName rightName
    RamTruncatedSubtract.command ((a-b : ℚ≥0) : ℚ) hB (num_bound ha) (den_bound ha) (num_bound hb) (den_bound hb)
    hlfresh hrfresh hrretain (by simpa only [value_eq] using hop) σ hσ
  obtain ⟨τ,rs,ps⟩ := save_spec B target (a-b) ((num_bound hout).trans_lt hMB) ((den_bound hout).trans_lt hMB) htarget ν pr
  exact ⟨τ,(rr.seq rs).mono (by omega),ps⟩

end Lax455465Proofs.RamScalarDifference
