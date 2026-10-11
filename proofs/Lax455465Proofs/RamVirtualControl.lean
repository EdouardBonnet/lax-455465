import Lax455465Proofs.RamVirtualArithmetic
import Lax455465Proofs.RamVirtualState

namespace Lax455465Proofs.RamVirtualControl

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamVirtualCore RamVirtualArithmetic RamVirtualProgram RamVirtualState

theorem jzero_core_spec (B w pc : ℕ) (m : SparseRam.Memory) (a label : ℕ)
    (h1 : 1 < B) (hM : 2 ^ w < B) (ha : a < B) (hlabel : label < B)
    (hpc : pc + 1 < B) (hlen : m.length < B) (hwords : SparseBounds.MemoryWords w m) :
    Spec B (Working w pc m) (instruction (.jzero a label))
      (fun _ τ => Core w (if SparseRam.lookup m (a % 2 ^ w) = 0 then label else pc + 1) m τ)
      (16 * m.length + 26) := by
  let value := SparseRam.lookup m (a % 2 ^ w)
  have hvalue := (SparseBounds.lookup_bound w m (a % 2 ^ w) hwords).trans hM
  have hbody : Spec B (fun σ => Working w pc m σ ∧ σ.vars "vm.left" = value)
      (.ite (.eq (.var "vm.left") (.lit 0)) (.assign "vm.pc" (.lit label)) increment)
      (fun _ τ => Core w (if value = 0 then label else pc + 1) m τ) 8 := by
    rintro σ ⟨⟨⟨hrep, hσpc, hσM, hσw⟩, hA, hV⟩, hσvalue⟩
    run_vcg
    all_goals simp_all [Core, RamSparseRead.Representation]
  have h := operand_spec B w pc m a _ 8 _ h1 hM ha hlen hwords hbody
  simpa only [instruction, Nat.add_assoc, Nat.reduceAdd, value] using h

/-- EOF branches consult the simulated cursor, while preserving both
sequential and indexed input views and all virtual output records. -/
theorem jeof_spec (B w : ℕ) (s : SparseRam.SparseState) (label : ℕ)
    (hlabel : label < B) (hlen : s.input.length < B) (hpc : s.pc + 1 < B) (h1 : 1 < B) :
    Spec B (Represents w s) (instruction (.jeof label))
      (fun _ τ => Represents w { s with pc := if s.inp.isEmpty then label else s.pc + 1 } τ) 8 := by
  rintro σ ⟨hcore, htapes⟩
  have hcursorB := htapes.2.2.1.trans_lt hlen
  have heof := empty_iff_cursor s σ htapes
  have hinputlen := htapes.2.1
  have hpcσ := hcore.2.1
  have hnil : s.inp.isEmpty = true ↔ σ.vars "vm.cursor" = σ.vars "vm.inputLength" := by
    simpa only [List.isEmpty_iff, hinputlen] using heof
  run_vcg
  all_goals simp_all [Represents, Core, Tapes, Prefix, RamSparseRead.Representation]

end Lax455465Proofs.RamVirtualControl
