import Lax455465Proofs.RamMinimum

namespace Lax455465Proofs.RamMaximum

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational
open scoped NNRat

open RamMinimum

def command : Com := .seq RamComparison.compareFraction
  (.ite (.eq (.var "cmp.le") (.lit 1)) right left)

/-- Exact native maximum of canonical nonnegative rational operands,
including equality and zero, without renormalizing either operand. -/
theorem command_spec (B M : ℕ) (a b : ℚ≥0) (hB : 2*M^2+3 < B)
    (han : a.num ≤ M) (had : a.den ≤ M) (hbn : b.num ≤ M) (hbd : b.den ≤ M) :
    Spec B (fractionInputs 0 a.num a.den 0 b.num b.den) command
      (fun _ τ => FractionOutput (max (a : ℚ) (b : ℚ)) τ) 50 := by
  have hM : M < B := by nlinarith
  have h1 : 1 < B := by nlinarith
  have ha : fractionValue 0 a.num a.den = (a : ℚ) := by
    simp only [fractionValue,show ¬(0:ℕ)=1 by decide,if_false]
    exact congrArg (fun q : ℚ≥0 => (q : ℚ)) (NNRat.num_div_den a)
  have hb : fractionValue 0 b.num b.den = (b : ℚ) := by
    simp only [fractionValue,show ¬(0:ℕ)=1 by decide,if_false]
    exact congrArg (fun q : ℚ≥0 => (q : ℚ)) (NNRat.num_div_den b)
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
    obtain ⟨τ,hr,ht⟩ := right_spec B b h1 (hbn.trans_lt hM) (hbd.trans_lt hM) ν hinputsν.2.2.2
    refine ⟨τ,hcompare.seq (Run.ite_true (by simpa only [hflag,decide_true] using hc) hr),?_⟩
    simpa only [max_eq_right hab] using ht
  · have hflag : ¬ν.vars "cmp.le" = 1 := fun hf => hab (by simpa only [ha,hb] using hpost.2.mp hf)
    obtain ⟨τ,hr,ht⟩ := left_spec B a h1 (han.trans_lt hM) (had.trans_lt hM) ν
      ⟨hinputsν.1,hinputsν.2.1,hinputsν.2.2.1⟩
    refine ⟨τ,hcompare.seq (Run.ite_false (by simpa only [hflag,decide_false] using hc) hr),?_⟩
    simpa only [max_eq_left (le_of_not_ge hab)] using ht

end Lax455465Proofs.RamMaximum
