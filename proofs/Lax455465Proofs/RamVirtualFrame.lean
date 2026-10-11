import Lax455465Proofs.RamVirtualState
import Lax455465Proofs.RamVirtualArithmetic

namespace Lax455465Proofs.RamVirtualFrame

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamVirtualCore RamVirtualArithmetic RamVirtualProgram RamVirtualState

/-- These instructions preserve the virtual input/output buffers and their
counters, so their memory-and-counter proofs lift to complete source states. -/
def Quiet : Lax808846.Ram.Instr → Prop
  | .read _ | .write _ | .halt => False
  | _ => True

theorem quiet_arrays (i : Lax808846.Ram.Instr) (hq : Quiet i) :
    "vm.input" ∉ (instruction i).warrs ∧ "vm.output" ∉ (instruction i).warrs := by
  cases i <;> simp_all [Quiet, instruction, binary, operands, RamWordOps.binary,
    RamWordOps.reduce, RamWordOps.shift, RamWordOps.complement, writeBack,
    RamSparseRead.read, RamSparseRead.write, RamSparseMemory.lookup,
    RamSparseMemory.scanStep, RamSparseMemory.put, increment, Com.warrs]

theorem quiet_variables (i : Lax808846.Ram.Instr) (hq : Quiet i) :
    ∀ x ∈ ["vm.inputLength", "vm.cursor", "vm.outputLength", "vm.running"],
      x ∉ (instruction i).wvars := by
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
    cases i <;> simp_all [Quiet, instruction, binary, operands, RamWordOps.binary,
      RamWordOps.reduce, RamWordOps.shift, RamWordOps.complement, writeBack,
      RamSparseRead.read, RamSparseRead.write, RamSparseMemory.lookup,
      RamSparseMemory.scanStep, RamSparseMemory.put, increment, Com.wvars]

/-- Lift an instruction proof for its memory and counter to a proof for
its complete virtual state, preserving the buffered tape representations. -/
theorem lift_spec (B w K : ℕ) (i : Lax808846.Ram.Instr) (s t : SparseRam.SparseState)
    (P : Env → Prop) (hq : Quiet i)
    (ht : t.input = s.input ∧ t.inp = s.inp ∧ t.out = s.out)
    (hspec : Spec B P (instruction i) (fun _ τ => Core w t.pc t.memory τ) K)
    (hpre : ∀ σ, Represents w s σ → s.memory.length < (σ.arrs "vm.addresses").length →
      s.memory.length < (σ.arrs "vm.values").length → P σ) :
    Spec B (fun σ => Represents w s σ ∧ σ.vars "vm.running" = 1 ∧
      s.memory.length < (σ.arrs "vm.addresses").length ∧
      s.memory.length < (σ.arrs "vm.values").length) (instruction i)
      (fun _ τ => Represents w t τ ∧ τ.vars "vm.running" = 1) K := by
  rintro σ ⟨hrep, hrunning, hA, hV⟩
  obtain ⟨τ, hrun, hcore⟩ := hspec σ (hpre σ hrep hA hV)
  have harr := quiet_arrays i hq
  have hvar := quiet_variables i hq
  have htapes := tapes_frame hrun s hrep.2 harr.1 harr.2
    (hvar _ (by simp)) (hvar _ (by simp)) (hvar _ (by simp))
  have htapes' : Tapes t τ := by simpa only [Tapes, ht.1, ht.2.1, ht.2.2] using htapes
  exact ⟨τ, hrun, ⟨hcore, htapes'⟩,
    (hrun.frame_var _ (hvar _ (by simp))).trans hrunning⟩

end Lax455465Proofs.RamVirtualFrame
