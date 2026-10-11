import Lax455465Proofs.RamVirtualInstruction

namespace Lax455465Proofs.RamVirtualDispatch

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamVirtualCore RamVirtualProgram RamVirtualState RamVirtualInstruction

/-- Fetch mirrors the fixed dispatch tree, including falling outside the
source program. Its runtime argument is only the virtual program counter. -/
def fetch : List Lax808846.Ram.Instr → ℕ → ℕ → Option Lax808846.Ram.Instr
  | [], _, _ => none
  | i :: rest, offset, pc => if pc = offset then some i else fetch rest (offset + 1) pc

theorem fetch_eq (p : List Lax808846.Ram.Instr) (offset pc : ℕ) :
    fetch p offset pc = if offset ≤ pc then p[pc - offset]? else none := by
  induction p generalizing offset with
  | nil => simp [fetch]
  | cons i rest ih =>
    by_cases he : pc = offset
    · subst pc; simp [fetch]
    · rw [fetch, if_neg he, ih]
      by_cases hlo : offset ≤ pc
      · have hsucc : offset + 1 ≤ pc := by omega
        have hsub : pc - offset = (pc - (offset + 1)) + 1 := by omega
        simp [hlo, hsucc, hsub]
      · have hsucc : ¬offset + 1 ≤ pc := by omega
        simp [hlo, hsucc]

def Result (w : ℕ) (s : SparseRam.SparseState) (p : List Lax808846.Ram.Instr) (offset : ℕ)
    (τ : Env) : Prop :=
  match fetch p offset s.pc with
  | none => Represents w s τ ∧ τ.vars "vm.running" = 0
  | some i => RamVirtualInstruction.Result w s i τ

/-- A fixed dispatch tree adds at most four native operations per source
instruction. Its instruction bodies retain the exact virtual semantics. -/
theorem dispatch_spec (B w : ℕ) (s : SparseRam.SparseState) (p : List Lax808846.Ram.Instr)
    (offset : ℕ) (hB : 2 * (2 ^ w) ^ 2 + 3 < B)
    (hlit : ∀ i ∈ p, LiteralsFit B i) (hoff : offset + p.length < B)
    (hwords : SparseBounds.MemoryWords w s.memory)
    (hinput : s.input.length < B) (hinputWords : ∀ x ∈ s.input, x < B)
    (hpc : s.pc + 1 < B) (hmem : s.memory.length + 1 < B) (hout : s.out.length + 1 < B) :
    Spec B (Ready w s) (dispatch p offset) (fun _ τ => Result w s p offset τ)
      (4 * p.length + 32 * s.memory.length + 100) := by
  induction p generalizing offset with
  | nil =>
    exact ((stop_spec B w s (by omega)).pre (fun _ h => h.1)).mono (by simp)
  | cons i rest ih =>
    rintro σ hready
    have hpcσ := hready.1.1.2.1
    have hpcB : σ.vars "vm.pc" < B := by rw [hpcσ]; omega
    have hoffB : offset < B := by simp only [List.length_cons] at hoff; omega
    by_cases he : s.pc = offset
    · have hcond : (Cond.eq (.var "vm.pc") (.lit offset)).evalB B σ = some true := by
        rw [evalB_condEq_iff]
        exact ⟨s.pc, offset, by simpa only [hpcσ] using evalB_var hpcB, evalB_lit hoffB, by simp [he]⟩
      obtain ⟨τ, hrun, hpost⟩ := instruction_spec B w s i hB (hlit i List.mem_cons_self)
        hwords hinput hinputWords hpc hmem hout σ hready
      refine ⟨τ, (Run.ite_true hcond hrun).mono ?_, ?_⟩
      · simp only [Cond.size, Expr.size, List.length_cons]; omega
      · simpa only [Result, fetch, if_pos he] using hpost
    · have hcond : (Cond.eq (.var "vm.pc") (.lit offset)).evalB B σ = some false := by
        rw [evalB_condEq_iff]
        exact ⟨s.pc, offset, by simpa only [hpcσ] using evalB_var hpcB, evalB_lit hoffB, by simp [he]⟩
      obtain ⟨τ, hrun, hpost⟩ := ih (offset + 1)
        (fun j hj => hlit j (List.mem_cons_of_mem i hj)) (by simp only [List.length_cons] at hoff; omega) σ hready
      refine ⟨τ, (Run.ite_false hcond hrun).mono ?_, ?_⟩
      · simp only [Cond.size, Expr.size, List.length_cons]; omega
      · simpa only [Result, fetch, if_neg he] using hpost

/-- At offset zero, the native dispatch implements the actual registered
source program's single-step function. -/
theorem result_zero (w : ℕ) (s : SparseRam.SparseState) (p : Lax808846.Ram.Program) (τ : Env) :
    Result w s p 0 τ =
      match SparseRam.step w p s with
      | none => Represents w s τ ∧ τ.vars "vm.running" = 0
      | some t => Represents w t τ ∧ τ.vars "vm.running" = 1 := by
  simp only [Result, fetch_eq, Nat.zero_le, if_true, Nat.sub_zero, SparseRam.step]
  cases hi : p[s.pc]? with
  | none => rfl
  | some i =>
    simp only [RamVirtualInstruction.Result, Option.bind_some]
    cases SparseRam.effect w i s <;> rfl

end Lax455465Proofs.RamVirtualDispatch
