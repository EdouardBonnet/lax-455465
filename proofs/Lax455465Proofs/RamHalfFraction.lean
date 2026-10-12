import Lax455465Proofs.RamUnsignedBuffer
import Lax455465Proofs.RamRegionContext

namespace Lax455465Proofs.RamHalfFraction
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamArithmetic RamRegionContext
open scoped NNRat

def command : Com := .seq (.assign "rat.d" (.mul (.lit 2) (.var "rat.d"))) normalizeFraction

/-- Halve a nonnegative rational by doubling its denominator and reducing;
this preserves canonical encoding, including the zero numerator case. -/
theorem command_spec (B M : ℕ) (q : ℚ≥0) (h2 : 2 < B) (hB : 2*M < B)
    (hq : LpInputSize.Height M (q : ℚ)) :
    Spec B (fun σ => FractionOutput (q : ℚ) σ ∧ σ.vars "rat.s"=0) command
      (fun _ τ => FractionOutput ((q/2 : ℚ≥0) : ℚ) τ ∧ τ.vars "rat.s"=0) (36*(2*M).size+20) := by
  have hnum : q.num < B := (num_bound hq).trans_lt (by omega)
  have hden : q.den < B := (den_bound hq).trans_lt (by omega)
  have htwoden : 2*q.den < B := (Nat.mul_le_mul_left 2 (den_bound hq)).trans_lt hB
  have hquot : (q.num : ℚ)/(q.den : ℚ)=(q : ℚ) := by
    exact congrArg (fun x : ℚ≥0 => (x : ℚ)) (NNRat.num_div_den q)
  have hvalue : fractionValue 0 q.num (2*q.den)=((q/2 : ℚ≥0) : ℚ) := by
    simp only [fractionValue,show ¬(0 : ℕ)=1 by decide,if_false,Nat.cast_mul,Nat.cast_ofNat,NNRat.coe_div]
    rw [mul_comm (2 : ℚ),div_mul_eq_div_div,hquot]
    norm_num
  rintro σ ⟨hqσ,hsσ⟩
  have hnσ : σ.vars "rat.n"=q.num := by simpa only [NNRat.natAbs_num_coe] using hqσ.2.1
  have hdσ : σ.vars "rat.d"=q.den := by simpa only [NNRat.den_coe] using hqσ.2.2.1
  let ν := σ.setVar "rat.d" (2*q.den)
  have r1 : Run B (.assign "rat.d" (.mul (.lit 2) (.var "rat.d"))) σ ν 4 :=
    Run.assign (evalB_bin (op := .mul) (evalB_lit h2)
      (by rw [evalB_var_iff]; exact ⟨hdσ.symm,hdσ ▸ hden⟩) htwoden)
  obtain ⟨τ,r2,p2⟩ := normalizeFraction_output_spec B 0 q.num (2*q.den) (by omega) hnum htwoden
    (by have := q.den_pos; omega) ν
    ⟨by simpa [ν] using hnσ,by simp [ν],by simpa [ν] using hsσ⟩
  have hsize : (2*q.den).size ≤ (2*M).size := Nat.size_le_size (Nat.mul_le_mul_left 2 (den_bound hq))
  exact ⟨τ,(r1.seq r2).mono (by omega),by simpa only [hvalue] using p2,
    ((r1.seq r2).frame_var "rat.s" (by decide)).trans hsσ⟩

end Lax455465Proofs.RamHalfFraction
