import Lax455465Proofs.RamScalarBinary
import Lax455465Proofs.UnsignedHeight

namespace Lax455465Proofs.RamScalarProduct
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamUnsignedScalar
open scoped NNRat

def command (leftName rightName target : String) : Com :=
  .seq (RamScalarBinary.command leftName rightName multiplyFraction) (save target)

/-- Multiply two stored unsigned rationals and save their canonical product.
The result bound follows from the input heights. -/
theorem command_spec (B M : ℕ) (a b : ℚ≥0) (leftName rightName target : String)
    (hB : 2*M^2+3<B) (han : a.num≤M) (had : a.den≤M) (hbn : b.num≤M) (hbd : b.den≤M)
    (hlfresh : leftName++".n"≠"rat.s" ∧ leftName++".d"≠"rat.s" ∧ leftName++".d"≠"rat.n")
    (hrfresh : rightName++".n"≠"rat.s" ∧ rightName++".d"≠"rat.s" ∧ rightName++".d"≠"rat.n")
    (hrretain : rightName++".n"∉(Com.seq (load leftName) (RamUnsignedArithmetic.copy "left")).wvars ∧
      rightName++".d"∉(Com.seq (load leftName) (RamUnsignedArithmetic.copy "left")).wvars)
    (htarget : target++".n"≠"rat.d") :
    Spec B (fun σ => Stored leftName a σ ∧ Stored rightName b σ) (command leftName rightName target)
      (fun _ τ => Stored target (a*b) τ) (36*(a.den*b.den).size+92) := by
  have ha : LpInputSize.Height M (a : ℚ) := ⟨by simpa only [NNRat.natAbs_num_coe] using han,by simpa only [NNRat.den_coe] using had⟩
  have hb : LpInputSize.Height M (b : ℚ) := ⟨by simpa only [NNRat.natAbs_num_coe] using hbn,by simpa only [NNRat.den_coe] using hbd⟩
  have hp := LpInputSize.height_mul ha hb
  have hpnum : (a*b).num<B := (show (a*b).num≤M*M by simpa only [←NNRat.coe_mul,NNRat.natAbs_num_coe] using hp.1).trans_lt (by nlinarith)
  have hpden : (a*b).den<B := (show (a*b).den≤M*M by simpa only [←NNRat.coe_mul,NNRat.den_coe] using hp.2).trans_lt (by nlinarith)
  have hop := multiplyFraction_spec B M 0 a.num a.den 0 b.num b.den hB (by omega) (by omega) han had hbn hbd a.den_pos b.den_pos
  rintro σ hσ
  obtain ⟨ν,rr,pr⟩ := RamScalarBinary.command_spec B M (36*(a.den*b.den).size+64) a b leftName rightName multiplyFraction ((a*b : ℚ≥0) : ℚ)
    hB han had hbn hbd hlfresh hrfresh hrretain (by simpa only [RamUnsignedArithmetic.value,NNRat.coe_mul] using hop) σ hσ
  obtain ⟨τ,rs,ps⟩ := save_spec B target (a*b) hpnum hpden htarget ν pr
  exact ⟨τ,(rr.seq rs).mono (by omega),ps⟩

end Lax455465Proofs.RamScalarProduct
