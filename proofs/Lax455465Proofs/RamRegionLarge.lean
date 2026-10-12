import Lax455465Proofs.RamScalarComparison
import Lax455465Proofs.RamRegionContext

namespace Lax455465Proofs.RamRegionLarge
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamUnsignedScalar RamRegionContext
open scoped NNRat

def command : Com := .seq (RamScalarComparison.command "round.largeThreshold" "region.outMass")
  (.seq (.assign "large.out" (.var "cmp.le"))
    (.seq (RamScalarComparison.command "round.largeThreshold" "region.inMass")
      (.assign "region.large" (.mul (.var "large.out") (.var "cmp.le")))))

def Input (threshold outMass inMass : ℚ≥0) (σ : Env) : Prop :=
  Stored "round.largeThreshold" threshold σ ∧ Stored "region.outMass" outMass σ ∧ Stored "region.inMass" inMass σ

theorem command_spec (B M : ℕ) (threshold outMass inMass : ℚ≥0) (hB : 2*M^2+3<B)
    (ht : LpInputSize.Height M (threshold : ℚ)) (ho : LpInputSize.Height M (outMass : ℚ))
    (hi : LpInputSize.Height M (inMass : ℚ)) :
    Spec B (Input threshold outMass inMass) command
      (fun _ τ => Input threshold outMass inMass τ ∧ τ.vars "region.large"=
        if (threshold : ℚ)≤outMass ∧ (threshold : ℚ)≤ inMass then 1 else 0) 134 := by
  rintro σ ⟨htσ,hoσ,hiσ⟩
  obtain ⟨ν,ro,po⟩ := RamScalarComparison.command_spec B M threshold outMass "round.largeThreshold" "region.outMass" hB
    (num_bound ht) (den_bound ht) (num_bound ho) (den_bound ho) (by decide) (by decide) (by decide) σ ⟨htσ,hoσ⟩
  let outFlag : ℕ := if (threshold : ℚ)≤outMass then 1 else 0
  have hoFlag : ν.vars "cmp.le"=outFlag := po
  have h1 : 1<B := by nlinarith
  have hoB : ν.vars "cmp.le"<B := by rw [po]; split_ifs <;> omega
  let μ := ν.setVar "large.out" outFlag
  have rs : Run B (.assign "large.out" (.var "cmp.le")) ν μ 2 := Run.assign (by rw [evalB_var_iff]; exact ⟨po.symm,hoB⟩)
  have rprior := ro.seq rs
  obtain ⟨ξ,ri,pi⟩ := RamScalarComparison.command_spec B M threshold inMass "round.largeThreshold" "region.inMass" hB
    (num_bound ht) (den_bound ht) (num_bound hi) (den_bound hi) (by decide) (by decide) (by decide) μ
    ⟨by simpa only [Stored,String.reduceAppend,rprior.frame_var "round.largeThreshold.n" (by decide),rprior.frame_var "round.largeThreshold.d" (by decide)] using htσ,
      by simpa only [Stored,String.reduceAppend,rprior.frame_var "region.inMass.n" (by decide),rprior.frame_var "region.inMass.d" (by decide)] using hiσ⟩
  let inFlag : ℕ := if (threshold : ℚ)≤ inMass then 1 else 0
  have hiFlag : ξ.vars "cmp.le"=inFlag := pi
  have hout : ξ.vars "large.out"=outFlag := by simpa only [μ,vars_setVar,if_true,ri.frame_var "large.out" (by decide)]
  have hoBound : outFlag≤1 := by dsimp [outFlag]; split_ifs <;> omega
  have hiBound : inFlag≤1 := by dsimp [inFlag]; split_ifs <;> omega
  have hprod : outFlag*inFlag<B := (Nat.mul_le_mul hoBound hiBound).trans_lt (by simpa using h1)
  let τ := ξ.setVar "region.large" (outFlag*inFlag)
  have rm : Run B (.assign "region.large" (.mul (.var "large.out") (.var "cmp.le"))) ξ τ 4 :=
    Run.assign (evalB_bin (op := .mul) (by rw [evalB_var_iff]; exact ⟨hout.symm,hout ▸ hoBound.trans_lt h1⟩)
      (by rw [evalB_var_iff]; exact ⟨hiFlag.symm,hiFlag ▸ hiBound.trans_lt h1⟩) hprod)
  have rr := ro.seq (rs.seq (ri.seq rm))
  refine ⟨τ,rr,?_,?_⟩
  · exact ⟨by simpa only [Stored,String.reduceAppend,rr.frame_var "round.largeThreshold.n" (by decide),rr.frame_var "round.largeThreshold.d" (by decide)] using htσ,
      by simpa only [Stored,String.reduceAppend,rr.frame_var "region.outMass.n" (by decide),rr.frame_var "region.outMass.d" (by decide)] using hoσ,
      by simpa only [Stored,String.reduceAppend,rr.frame_var "region.inMass.n" (by decide),rr.frame_var "region.inMass.d" (by decide)] using hiσ⟩
  · simp only [τ,vars_setVar,if_true,outFlag,inFlag]
    split_ifs <;> simp_all

end Lax455465Proofs.RamRegionLarge
