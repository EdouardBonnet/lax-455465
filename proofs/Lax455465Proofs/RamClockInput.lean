import Lax455465Proofs.RamInputCopy
import Lax455465Proofs.RamArrayCopy

namespace Lax455465Proofs.RamClockInput
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState

def command : Com := .seq RamInputCopy.copy
  (.seq (RamArrayCopy.command "input.data" "lp.word" "input.length")
    (.assign "lp.position" (.var "input.length")))

theorem command_spec (B : ℕ) (xs : List ℕ) (h1 : 1 < B) (hlen : xs.length < B)
    (hwords : ∀ a∈xs,a < B) :
    Spec B (fun σ => σ.inp=xs.length::xs ∧ xs.length ≤ (σ.arrs "input.data").length ∧
      xs.length ≤ (σ.arrs "lp.word").length) command
      (fun _ τ => Prefix xs "lp.word" τ ∧ τ.vars "lp.position"=xs.length) (24*xs.length+15) := by
  rintro σ ⟨hinp,hinput,hroom⟩
  obtain ⟨ν,r1,hcount,_,hp⟩ := RamInputCopy.copy_spec B xs h1 hlen hwords σ ⟨hinp,hinput⟩
  obtain ⟨μ,r2,p2⟩ := RamArrayCopy.command_spec B xs "input.data" "lp.word" "input.length" h1 hlen hwords
    (by decide) (by decide) ν ⟨hp,hcount,by rwa [RamFrames.run_array_length r1]⟩
  have hcμ : μ.vars "input.length"=xs.length := (r2.frame_var _ (by decide)).trans hcount
  let τ := μ.setVar "lp.position" xs.length
  have r3 : Run B (.assign "lp.position" (.var "input.length")) μ τ 2 := Run.assign (by
    rw [evalB_var_iff]; exact ⟨hcμ.symm,hcμ ▸ hlen⟩)
  exact ⟨τ,(r1.seq (r2.seq r3)).mono (by omega),p2.2,by simp [τ]⟩

end Lax455465Proofs.RamClockInput
