import Lax455465Proofs.RamScalarComparison
import Lax455465Proofs.RamBallMass

namespace Lax455465Proofs.RamRegionDirection

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamUnsignedScalar
open scoped NNRat

def command : Com := .seq (RamScalarComparison.command "region.outMass" "region.inMass")
  (.assign "region.outward" (.var "cmp.le"))

/-- Choose the smaller actual residual ball mass, resolving equality in
favor of the outward direction exactly as the region-loop definition does. -/
theorem command_spec (B M : ℕ) {n : ℕ} (weights outDistance inDistance : Fin n → ℚ≥0)
    (radius : ℚ≥0) (hB : 2*M^2+3 < B)
    (hon : (BallMassData.mass weights outDistance radius).num ≤ M)
    (hod : (BallMassData.mass weights outDistance radius).den ≤ M)
    (hin : (BallMassData.mass weights inDistance radius).num ≤ M)
    (hid : (BallMassData.mass weights inDistance radius).den ≤ M) :
    Spec B (fun σ => Stored "region.outMass" (BallMassData.mass weights outDistance radius) σ ∧
      Stored "region.inMass" (BallMassData.mass weights inDistance radius) σ)
      command (fun _ τ => Stored "region.outMass" (BallMassData.mass weights outDistance radius) τ ∧
        Stored "region.inMass" (BallMassData.mass weights inDistance radius) τ ∧
        τ.vars "region.outward" = if RegionSelection.direction (fun v => (weights v : ℚ))
          (fun v => (outDistance v : ℚ)) (fun v => (inDistance v : ℚ)) radius then 1 else 0) 66 := by
  intro σ hσ
  obtain ⟨ν,rc,pc⟩ := RamScalarComparison.command_spec B M (BallMassData.mass weights outDistance radius)
    (BallMassData.mass weights inDistance radius) "region.outMass" "region.inMass" hB hon hod hin hid
    (by decide) (by decide) (by decide) σ hσ
  let flag := if (BallMassData.mass weights outDistance radius : ℚ) ≤ (BallMassData.mass weights inDistance radius : ℚ) then 1 else 0
  have hf : ν.vars "cmp.le" < B := by rw [pc]; split_ifs <;> nlinarith
  have rsave : Run B (.assign "region.outward" (.var "cmp.le")) ν (ν.setVar "region.outward" flag) 2 :=
    Run.assign (by rw [evalB_var_iff]; exact ⟨pc.symm,hf⟩)
  have rr := rc.seq rsave
  refine ⟨ν.setVar "region.outward" flag,rr,?_,?_,?_⟩
  · simpa only [Stored,String.reduceAppend,rr.frame_var "region.outMass.n" (by decide),rr.frame_var "region.outMass.d" (by decide)] using hσ.1
  · simpa only [Stored,String.reduceAppend,rr.frame_var "region.inMass.n" (by decide),rr.frame_var "region.inMass.d" (by decide)] using hσ.2
  · simp only [vars_setVar,if_true,flag,RegionSelection.direction,decide_eq_true_eq,←BallMassData.coe_mass]

end Lax455465Proofs.RamRegionDirection
