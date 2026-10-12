import Lax455465Proofs.SupportData
import Lax455465Proofs.RegionBudget
import Lax455465Proofs.RamBitSize

namespace Lax455465Proofs.RamGridBudget
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

def finish : Com := .assign "round.steps" (.add (.mul (.lit 2) (.var "size.count")) (.lit 2))
def command : Com := .seq (.assign "size.value" (.var "round.support")) (.seq RamBitSize.word finish)

/-- Compute the exact finite logarithmic grid budget by repeated integer
halving of the runtime support count. No real logarithm is executed. -/
theorem command_spec (B p : ℕ) (hp : 0<p) (hB : 2*p+4<B) :
    Spec B (fun σ => σ.vars "round.support"=p) command
      (fun _ τ => τ.vars "round.support"=p ∧ τ.vars "round.steps"=RegionBudget.steps p)
      (12*p.size+14) := by
  have hsize : p.size≤p := Nat.size_le.mpr Nat.lt_two_pow_self
  have hk : 2*p.size+2=RegionBudget.steps p := by rw [SupportData.size_log p hp]; unfold RegionBudget.steps; omega
  rintro σ hσ
  let ν := σ.setVar "size.value" p
  have rstart : Run B (.assign "size.value" (.var "round.support")) σ ν 2 :=
    Run.assign (by rw [evalB_var_iff]; exact ⟨hσ.symm,hσ ▸ (by omega : p<B)⟩)
  obtain ⟨μ,rw,pw⟩ := RamBitSize.word_spec B p (by omega) (by omega) ν (by simp [ν])
  let τ := μ.setVar "round.steps" (RegionBudget.steps p)
  have rsave : Run B finish μ τ 6 := by
    change Run B finish μ (μ.setVar "round.steps" (RegionBudget.steps p)) 6
    rw [←hk]
    exact Run.assign (evalB_bin (op := .add) (m := 2*p.size) (n := 2)
      (evalB_bin (op := .mul) (m := 2) (n := p.size) (evalB_lit (by omega))
        (by rw [evalB_var_iff]; exact ⟨pw.2.symm,pw.2 ▸ (by omega : p.size<B)⟩) (by dsimp [Bop.apply]; omega))
      (evalB_lit (by omega)) (by dsimp [Bop.apply]; omega))
  have rr := rstart.seq (rw.seq rsave)
  exact ⟨τ,rr.mono (by omega),(rr.frame_var _ (by decide)).trans hσ,by simp [τ]⟩

end Lax455465Proofs.RamGridBudget
