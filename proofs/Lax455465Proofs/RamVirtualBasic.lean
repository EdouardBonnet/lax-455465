import Lax455465Proofs.RamVirtualArithmetic
import Lax455465Proofs.RamVirtualState

namespace Lax455465Proofs.RamVirtualBasic

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamVirtualCore RamVirtualArithmetic RamVirtualState

/-- The five bounded binary operations share the same native memory and
program-counter simulation. Shifts use their separate guarded command. -/
inductive Kind | add | sub | mul | div | and

def operation : Kind → Bop
  | .add => .add | .sub => .sub | .mul => .mul | .div => .div | .and => .and

def source (kind : Kind) (a b c : ℕ) : Lax808846.Ram.Instr :=
  match kind with
  | .add => .add a b c | .sub => .sub a b c | .mul => .mul a b c
  | .div => .div a b c | .and => .and a b c

def result (kind : Kind) (w : ℕ) (m : SparseRam.Memory) (b c : ℕ) : ℕ :=
  (operation kind).apply (SparseRam.lookup m (b % 2 ^ w)) (SparseRam.lookup m (c % 2 ^ w))

theorem result_bound (kind : Kind) (w : ℕ) (m : SparseRam.Memory) (b c : ℕ)
    (hwords : SparseBounds.MemoryWords w m) : result kind w m b c < 2 * (2 ^ w) ^ 2 + 3 := by
  have h := RamWordOps.basic_bounds w (SparseRam.lookup m (b % 2 ^ w))
    (SparseRam.lookup m (c % 2 ^ w)) (SparseBounds.lookup_bound _ _ _ hwords)
    (SparseBounds.lookup_bound _ _ _ hwords)
  cases kind with
  | add => exact h.1
  | sub => exact h.2.1
  | mul => exact h.2.2.1
  | div => exact h.2.2.2.1
  | and => exact h.2.2.2.2

theorem source_effect (kind : Kind) (w a b c : ℕ) (s : SparseRam.SparseState) :
    SparseRam.effect w (source kind a b c) s = some (SparseRam.assign w s a (result kind w s.memory b c)) := by
  cases kind <;> rfl

/-- Native execution implements the source instruction's exact sparse
transition, preserving both virtual input views, output, and running flag. -/
theorem instruction_spec (B w : ℕ) (kind : Kind) (s : SparseRam.SparseState) (a b c : ℕ)
    (hB : 2 * (2 ^ w) ^ 2 + 3 < B) (ha : a < B) (hb : b < B) (hc : c < B)
    (hwords : SparseBounds.MemoryWords w s.memory) (hpc : s.pc + 1 < B)
    (hlen : s.memory.length + 1 < B) :
    Spec B (fun σ => Represents w s σ ∧ σ.vars "vm.running" = 1 ∧
      s.memory.length < (σ.arrs "vm.addresses").length ∧
      s.memory.length < (σ.arrs "vm.values").length)
      (RamVirtualProgram.instruction (source kind a b c))
      (fun _ τ => Represents w (SparseRam.assign w s a (result kind w s.memory b c)) τ ∧
        τ.vars "vm.running" = 1) (32 * s.memory.length + 88) := by
  have h1 : 1 < B := by omega
  have hM : 2 ^ w < B := by nlinarith [Nat.two_pow_pos w]
  have hcore : Spec B (Working w s.pc s.memory)
      (RamVirtualProgram.instruction (source kind a b c))
      (fun _ τ => Core w (s.pc + 1) (SparseRam.write w s.memory a (result kind w s.memory b c)) τ)
      (32 * s.memory.length + 88) := by
    have h := RamVirtualArithmetic.binary_spec B w s.pc s.memory a b c (operation kind)
      h1 hM ha hb hc hwords ((result_bound kind w s.memory b c hwords).trans hB) hpc hlen
    cases kind <;> exact h
  rintro σ ⟨⟨hcoreσ, htapes⟩, hrunning, hA, hV⟩
  obtain ⟨τ, hrun, hpost⟩ := hcore σ ⟨hcoreσ, hA, hV⟩
  have hcommand : RamVirtualProgram.instruction (source kind a b c) =
      RamVirtualProgram.binary (operation kind) a b c := by cases kind <;> rfl
  have hinput : "vm.input" ∉ (RamVirtualProgram.instruction (source kind a b c)).warrs := by
    rw [hcommand]
    simp [RamVirtualProgram.binary,
      RamVirtualProgram.operands, RamWordOps.binary, RamWordOps.reduce,
      RamVirtualProgram.writeBack, RamSparseRead.read, RamSparseRead.write,
      RamSparseMemory.lookup, RamSparseMemory.scanStep, RamSparseMemory.put, RamVirtualProgram.increment, Com.warrs]
  have houtput : "vm.output" ∉ (RamVirtualProgram.instruction (source kind a b c)).warrs := by
    rw [hcommand]
    simp [RamVirtualProgram.binary,
      RamVirtualProgram.operands, RamWordOps.binary, RamWordOps.reduce,
      RamVirtualProgram.writeBack, RamSparseRead.read, RamSparseRead.write,
      RamSparseMemory.lookup, RamSparseMemory.scanStep, RamSparseMemory.put, RamVirtualProgram.increment, Com.warrs]
  have hvars : ∀ x ∈ ["vm.inputLength", "vm.cursor", "vm.outputLength", "vm.running"],
      x ∉ (RamVirtualProgram.instruction (source kind a b c)).wvars := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rw [hcommand]
    rcases hx with rfl | rfl | rfl | rfl <;>
      simp [RamVirtualProgram.binary,
        RamVirtualProgram.operands, RamWordOps.binary, RamWordOps.reduce,
        RamVirtualProgram.writeBack, RamSparseRead.read, RamSparseRead.write,
        RamSparseMemory.lookup, RamSparseMemory.scanStep, RamSparseMemory.put, RamVirtualProgram.increment, Com.wvars]
  have htapes' := tapes_frame hrun s htapes hinput houtput
    (hvars _ (by simp)) (hvars _ (by simp)) (hvars _ (by simp))
  exact ⟨τ, hrun, ⟨hpost, htapes'⟩, (hrun.frame_var _ (hvars _ (by simp))).trans hrunning⟩

end Lax455465Proofs.RamVirtualBasic
