import Lax455465Proofs.RamScalarProduct
import Lax455465Proofs.RamRegionContext

namespace Lax455465Proofs.RamLargeThreshold
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamUnsignedScalar RamRegionContext
open scoped NNRat

def threshold (total : ℚ≥0) : ℚ≥0 := total*(2/3 : ℚ≥0)
def factor : Com := .seq (.assign "round.largeFactor.n" (.lit 2)) (.assign "round.largeFactor.d" (.lit 3))
def command : Com := .seq factor (RamScalarProduct.command "round.total" "round.largeFactor" "round.largeThreshold")

theorem coe_threshold (total : ℚ≥0) : (threshold total : ℚ)=2*(total : ℚ)/3 := by
  rw [threshold,NNRat.coe_mul]
  change (total : ℚ)*(2/3 : ℚ)=2*(total : ℚ)/3
  ring

set_option maxHeartbeats 200000 in
/-- Compute the exact two-thirds total-mass threshold once for the region
loop's large-ball branch. -/
theorem command_spec (B M : ℕ) (total : ℚ≥0) (hM : 3≤M) (hB : 2*M^2+3<B)
    (ht : LpInputSize.Height M (total : ℚ)) :
    Spec B (Stored "round.total" total) command (fun _ τ => Stored "round.total" total τ ∧
      Stored "round.largeThreshold" (threshold total) τ) (36*(total.den*3).size+96) := by
  have hfn : (2/3 : ℚ≥0).num=2 := by
    rw [← NNRat.natAbs_num_coe]
    have hc : ((2/3 : ℚ≥0) : ℚ)=(2/3 : ℚ) := by norm_num
    rw [hc]
    norm_num
  have hfd : (2/3 : ℚ≥0).den=3 := by
    rw [← NNRat.den_coe]
    have hc : ((2/3 : ℚ≥0) : ℚ)=(2/3 : ℚ) := by norm_num
    rw [hc]
    norm_num
  have h2 : 2<B := by nlinarith
  have h3 : 3<B := by nlinarith
  have hfac : Spec B (fun _ => True) factor (fun _ τ => Stored "round.largeFactor" (2/3 : ℚ≥0) τ) 4 := by
    intro σ _
    let ν := σ.setVar "round.largeFactor.n" 2
    let τ := ν.setVar "round.largeFactor.d" 3
    have rn : Run B (.assign "round.largeFactor.n" (.lit 2)) σ ν 2 := Run.assign (evalB_lit h2)
    have rd : Run B (.assign "round.largeFactor.d" (.lit 3)) ν τ 2 := Run.assign (evalB_lit h3)
    refine ⟨τ,rn.seq rd,?_⟩
    exact ⟨(show τ.vars "round.largeFactor.n"=2 by rfl).trans hfn.symm,
      (show τ.vars "round.largeFactor.d"=3 by rfl).trans hfd.symm⟩
  have hb : LpInputSize.Height M ((2/3 : ℚ≥0) : ℚ) :=
    LpInputSize.height_mono (show LpInputSize.Height 3 ((2/3 : ℚ≥0) : ℚ) by norm_num [LpInputSize.Height]) hM
  rintro σ hσ
  obtain ⟨ν,rf,pf⟩ := hfac σ True.intro
  obtain ⟨τ,rp,pp⟩ := RamScalarProduct.command_spec B M total (2/3) "round.total" "round.largeFactor" "round.largeThreshold" hB
    (num_bound ht) (den_bound ht) (num_bound hb) (den_bound hb) (by decide) (by decide) (by decide) (by decide) ν
    ⟨by simpa only [Stored,String.reduceAppend,rf.frame_var "round.total.n" (by decide),rf.frame_var "round.total.d" (by decide)] using hσ,pf⟩
  have rr := rf.seq rp
  refine ⟨τ,rr.mono (by rw [hfd]; omega),?_,pp⟩
  simpa only [Stored,String.reduceAppend,rr.frame_var "round.total.n" (by decide),rr.frame_var "round.total.d" (by decide)] using hσ

end Lax455465Proofs.RamLargeThreshold
