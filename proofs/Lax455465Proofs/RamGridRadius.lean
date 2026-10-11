import Lax455465Proofs.RamUnsignedScalar

namespace Lax455465Proofs.RamGridRadius

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamUnsignedScalar RamRational
open scoped NNRat

def indexOperand : Com := .seq (.assign "right.s" (.lit 0))
  (.seq (.assign "right.n" (.var "radius.i")) (.assign "right.d" (.lit 1)))

def command : Com := .seq (load "round.gridStep") (.seq (RamUnsignedArithmetic.copy "left")
  (.seq indexOperand multiplyFraction))

/-- Form a grid radius from its stored exact step and the runtime integer
index. Multiplication normalizes the emitted numerator and denominator. -/
theorem command_spec (B M j : ℕ) (unit : ℚ≥0) (hB : 2*M^2+3 < B)
    (hun : unit.num ≤ M) (hud : unit.den ≤ M) (hj : j≤M) :
    Spec B (fun σ => Stored "round.gridStep" unit σ ∧ σ.vars "radius.i"=j)
      command (fun _ τ => FractionOutput ((unit*(j : ℚ≥0) : ℚ≥0) : ℚ) τ)
      (36*unit.den.size+82) := by
  have hM : M < B := by nlinarith
  have h1 : 1 < B := by nlinarith
  have hM1 : 1≤M := unit.den_pos.trans_le hud
  rintro σ ⟨hu,hi⟩
  obtain ⟨ν,rl,pl⟩ := load_spec B "round.gridStep" unit h1 (hun.trans_lt hM) (hud.trans_lt hM) (by decide) σ hu
  obtain ⟨μ,rc,pc⟩ := RamUnsignedArithmetic.copy_spec B unit "left" h1 (hun.trans_lt hM) (hud.trans_lt hM) (by decide) ν pl
  have hiμ : μ.vars "radius.i"=j := by
    have rr := rl.seq rc
    exact (rr.frame_var _ (by decide)).trans hi
  let ξ := ((μ.setVar "right.s" 0).setVar "right.n" j).setVar "right.d" 1
  have rn : Run B indexOperand μ ξ 6 := by
    refine (Run.assign (evalB_lit (by omega))).seq ((Run.assign ?_).seq (Run.assign (evalB_lit h1)))
    rw [evalB_var_iff]
    simpa only [vars_setVar,String.reduceEq,if_false] using And.intro hiμ.symm (hiμ ▸ hj.trans_lt hM)
  have pleft : ξ.vars "left.s"=0 ∧ ξ.vars "left.n"=unit.num ∧ ξ.vars "left.d"=unit.den := by
    simpa only [rn.frame_var "left.s" (by decide),rn.frame_var "left.n" (by decide),rn.frame_var "left.d" (by decide),String.reduceAppend] using pc
  obtain ⟨τ,rm,pm⟩ := multiplyFraction_spec B M 0 unit.num unit.den 0 j 1 hB
    (by omega) (by omega) hun hud hj hM1 unit.den_pos (by omega) ξ
    ⟨pleft.1,pleft.2.1,pleft.2.2,by simp [ξ],by simp [ξ],by simp [ξ]⟩
  refine ⟨τ,(rl.seq (rc.seq (rn.seq rm))).mono (by simp only [Nat.mul_one]; omega),?_⟩
  have huval := RamUnsignedArithmetic.value unit
  have hjval : fractionValue 0 j 1 = (j : ℚ) := by simp [fractionValue]
  simpa only [NNRat.coe_mul,NNRat.coe_natCast,huval,hjval] using pm

end Lax455465Proofs.RamGridRadius
