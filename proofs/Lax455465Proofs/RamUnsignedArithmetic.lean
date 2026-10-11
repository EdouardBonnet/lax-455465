import Lax455465Proofs.RamRational

namespace Lax455465Proofs.RamUnsignedArithmetic

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational
open scoped NNRat

def copy (side : String) : Com := .seq (.assign (side ++ ".s") (.lit 0))
  (.seq (.assign (side ++ ".n") (.var "rat.n")) (.assign (side ++ ".d") (.var "rat.d")))

/-- Copy a nonnegative canonical result to an operand, with canonical sign
zero even when the arithmetic convention permits a negative zero. -/
theorem copy_spec (B : ℕ) (q : ℚ≥0) (side : String) (h1 : 1 < B)
    (hn : q.num < B) (hd : q.den < B)
    (hfresh : side ++ ".s" ≠ "rat.n" ∧ side ++ ".s" ≠ "rat.d" ∧ side ++ ".n" ≠ "rat.d") :
    Spec B (FractionOutput (q : ℚ)) (copy side)
      (fun _ τ => τ.vars (side ++ ".s") = 0 ∧ τ.vars (side ++ ".n") = q.num ∧
        τ.vars (side ++ ".d") = q.den) 6 := by
  rintro σ ⟨hv,hnσ,hdσ,hs⟩
  have hn' : σ.vars "rat.n" = q.num := by simpa only [NNRat.natAbs_num_coe] using hnσ
  have hd' : σ.vars "rat.d" = q.den := by simpa only [NNRat.den_coe] using hdσ
  have hsN := Ne.symm hfresh.1
  have hsD := Ne.symm hfresh.2.1
  have hnD := Ne.symm hfresh.2.2
  run_vcg
  all_goals simp_all

theorem value (q : ℚ≥0) : fractionValue 0 q.num q.den = (q : ℚ) := by
  simp only [fractionValue,show ¬(0:ℕ)=1 by decide,if_false]
  exact congrArg (fun q : ℚ≥0 => (q : ℚ)) (NNRat.num_div_den q)

/-- Exact addition specialized to the unsigned operand convention. -/
theorem add_spec (B M : ℕ) (a b : ℚ≥0) (hB : 2*M^2+3 < B)
    (han : a.num ≤ M) (had : a.den ≤ M) (hbn : b.num ≤ M) (hbd : b.den ≤ M) :
    Spec B (fractionInputs 0 a.num a.den 0 b.num b.den) addFraction
      (fun _ τ => FractionOutput ((a+b : ℚ≥0) : ℚ) τ) (36*(a.den*b.den).size+96) := by
  simpa only [value,NNRat.coe_add] using addFraction_spec B M 0 a.num a.den 0 b.num b.den hB
    (by omega) (by omega) han had hbn hbd a.den_pos b.den_pos

end Lax455465Proofs.RamUnsignedArithmetic
