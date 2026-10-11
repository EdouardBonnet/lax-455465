import Lax455465Proofs.RamUnsignedArithmetic
import Lax455465Proofs.RamMinimum
import Lax455465Proofs.RamFractionPrimitives

namespace Lax455465Proofs.RamTruncatedSubtract

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational
open scoped NNRat

def value (a b : ℚ≥0) : ℚ≥0 := ⟨max ((a : ℚ)-(b : ℚ)) 0, le_max_right _ _⟩

def difference : Com := .seq (.assign "right.s" (.lit 1)) addFraction

def command : Com := .seq RamComparison.compareFraction
  (.ite (.eq (.var "cmp.le") (.lit 1)) RamFractionPrimitives.zero difference)

/-- Native clipped subtraction. The comparison branch returns canonical
zero when the difference is nonpositive. -/
theorem command_spec (B M : ℕ) (a b : ℚ≥0) (hB : 2*M^2+3 < B)
    (han : a.num ≤ M) (had : a.den ≤ M) (hbn : b.num ≤ M) (hbd : b.den ≤ M) :
    Spec B (fractionInputs 0 a.num a.den 0 b.num b.den) command
      (fun _ τ => FractionOutput (value a b : ℚ) τ) (36*(a.den*b.den).size+142) := by
  have h1 : 1 < B := by nlinarith
  have ha := RamUnsignedArithmetic.value a
  have hb := RamUnsignedArithmetic.value b
  rintro σ hinputs
  obtain ⟨ν,hcompare,hpost⟩ := RamComparison.compareFraction_spec B M 0 a.num a.den 0 b.num b.den
    hB (by omega) (by omega) han had hbn hbd a.den_pos b.den_pos σ hinputs
  have hinputsν : fractionInputs 0 a.num a.den 0 b.num b.den ν := by
    simpa only [fractionInputs,hcompare.frame_var "left.s" (by decide),hcompare.frame_var "left.n" (by decide),
      hcompare.frame_var "left.d" (by decide),hcompare.frame_var "right.s" (by decide),
      hcompare.frame_var "right.n" (by decide),hcompare.frame_var "right.d" (by decide)] using hinputs
  have hc : (Cond.eq (.var "cmp.le") (.lit 1)).evalB B ν = some (decide (ν.vars "cmp.le" = 1)) := by
    rw [evalB_condEq (evalB_var (by omega)) (evalB_lit h1)]
    congr 1
  by_cases hab : (a : ℚ) ≤ (b : ℚ)
  · have hflag : ν.vars "cmp.le" = 1 := hpost.2.mpr (by rwa [ha,hb])
    obtain ⟨τ,hr,ht⟩ := RamFractionPrimitives.zero_spec B h1 ν trivial
    refine ⟨τ,(hcompare.seq (Run.ite_true (d := difference) (by simpa only [hflag,decide_true] using hc) hr)).mono (by dsimp [Cond.size,Expr.size]; omega),?_⟩
    simpa only [value,NNRat.coe_mk,max_eq_right (sub_nonpos.mpr hab)] using ht
  · have hflag : ¬ν.vars "cmp.le" = 1 := fun hf => hab (by simpa only [ha,hb] using hpost.2.mp hf)
    let μ := ν.setVar "right.s" 1
    have hr : Run B (.assign "right.s" (.lit 1)) ν μ 2 := Run.assign (evalB_lit h1)
    have hμ : fractionInputs 0 a.num a.den 1 b.num b.den μ := by
      simpa [μ,fractionInputs,vars_setVar] using
        And.intro hinputsν.1 (And.intro hinputsν.2.1 (And.intro hinputsν.2.2.1 (And.intro (rfl : (1:ℕ)=1) hinputsν.2.2.2.2)))
    obtain ⟨τ,haRun,haPost⟩ := addFraction_spec B M 0 a.num a.den 1 b.num b.den hB
      (by omega) (by omega) han had hbn hbd a.den_pos b.den_pos μ hμ
    have hdifference : Run B difference ν τ (36*(a.den*b.den).size+98) := by
      have hh := hr.seq haRun
      unfold difference
      convert hh using 1 <;> omega
    refine ⟨τ,(hcompare.seq (Run.ite_false (c := RamFractionPrimitives.zero) (by simpa only [hflag,decide_false] using hc) hdifference)).mono (by dsimp [Cond.size,Expr.size]; omega),?_⟩
    have hnegative : fractionValue 1 b.num b.den = -(b : ℚ) := by
      simpa [fractionValue,neg_div] using congrArg Neg.neg hb
    change FractionOutput (max ((a : ℚ)-(b : ℚ)) 0) τ
    rw [max_eq_left (sub_nonneg.mpr (le_of_not_ge hab)),sub_eq_add_neg]
    simpa only [ha,hnegative] using haPost

end Lax455465Proofs.RamTruncatedSubtract
