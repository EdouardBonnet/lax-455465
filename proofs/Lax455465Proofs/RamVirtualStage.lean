import Lax455465Proofs.RamVirtualArithmetic

namespace Lax455465Proofs.RamVirtualStage

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamVirtualCore RamVirtualArithmetic RamVirtualProgram RamSparseRead

/-- A register-only phase preserves the virtual heap and the host buffer
bounds. This is the shared framing step for arithmetic and bit operations. -/
theorem working_frame {B K : ℕ} {c : Com} {σ τ : Env} (hr : Run B c σ τ K)
    (w pc : ℕ) (m : SparseRam.Memory) (h : Working w pc m σ)
    (harrays : c.warrs = [])
    (hvars : ∀ x ∈ ["vm.count", "vm.pc", "vm.modulus", "vm.width"], x ∉ c.wvars) :
    Working w pc m τ := by
  have ha := hr.frame_arrs_eqOn harrays
  have hcount := hr.frame_var "vm.count" (hvars _ (by simp))
  have hpc := hr.frame_var "vm.pc" (hvars _ (by simp))
  have hmod := hr.frame_var "vm.modulus" (hvars _ (by simp))
  have hw := hr.frame_var "vm.width" (hvars _ (by simp))
  simpa only [Working, Core, Representation, ha, hcount, hpc, hmod, hw] using h

/-- Compose any bounded register result with the native virtual write and
program-counter increment. The result is the exact source memory update. -/
theorem result_spec (B w pc : ℕ) (m : SparseRam.Memory) (target value : ℕ)
    (body : Com) (K : ℕ) (P : Env → Prop)
    (hbody : Spec B P body (fun _ τ => τ.vars "vm.result" = value) K)
    (harrays : body.warrs = [])
    (hvars : ∀ x ∈ ["vm.count", "vm.pc", "vm.modulus", "vm.width"], x ∉ body.wvars)
    (h1 : 1 < B) (hM : 2 ^ w < B) (htarget : target < B) (hv : value < B)
    (hpc : pc + 1 < B) (hlen : m.length + 1 < B) :
    Spec B (fun σ => Working w pc m σ ∧ P σ)
      (.seq body (writeBack (.lit target) (.var "vm.result")))
      (fun _ τ => Core w (pc + 1) (SparseRam.write w m target value) τ) (K + 40) := by
  have hstage : Spec B (fun σ => Working w pc m σ ∧ P σ) body
      (fun _ τ => Working w pc m τ ∧ τ.vars "vm.result" = value) K := by
    rintro σ ⟨hwork, hp⟩
    obtain ⟨τ, hr, hq⟩ := hbody σ hp
    exact ⟨τ, hr, working_frame hr w pc m hwork harrays hvars, hq⟩
  have hfinish := writeBack_register_spec B w pc m target value h1 hM htarget hv hpc hlen
  exact hstage.seq hfinish
    (fun _ _ _ h => ⟨h.1.1, h.2, h.1.2.1, h.1.2.2⟩)
    (fun _ _ _ _ _ h => h)

end Lax455465Proofs.RamVirtualStage
