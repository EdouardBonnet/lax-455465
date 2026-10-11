import Lax455465Proofs.RamVirtualState
import Lax455465Proofs.RamVirtualArithmetic

namespace Lax455465Proofs.RamVirtualOutput

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamVirtualCore RamVirtualArithmetic RamVirtualProgram RamVirtualState

private theorem prefix_append (words buffer : List ℕ) (value : ℕ)
    (h : ∀ i (hi : i < words.length), buffer[i]? = some words[i])
    (hroom : words.length < buffer.length) :
    ∀ i (hi : i < (words ++ [value]).length),
      (buffer.set words.length value)[i]? = some (words ++ [value])[i] := by
  intro i hi
  by_cases hlt : i < words.length
  · rw [← List.getElem_append_left' hlt, List.getElem?_set_ne (by omega : words.length ≠ i)]
    exact h i hlt
  · have he : i = words.length := by
      simp only [List.length_append, List.length_singleton] at hi
      omega
    subst i
    simp [List.getElem?_set_self hroom]

def append : Com := .seq (.store "vm.output" (.var "vm.outputLength") (remainder (.var "vm.left")))
  (.seq (.assign "vm.outputLength" (.add (.var "vm.outputLength") (.lit 1))) increment)

/-- The virtual output is stored in a host buffer, so it can be parsed and
rounded before the final LR certificate is emitted. -/
theorem append_spec (B w : ℕ) (s : SparseRam.SparseState) (value : ℕ)
    (h1 : 1 < B) (hM : 2 ^ w < B) (hv : value < B) (hpc : s.pc + 1 < B)
    (hlen : s.out.length + 1 < B) :
    Spec B (fun σ => Represents w s σ ∧ σ.vars "vm.running" = 1 ∧ σ.vars "vm.left" = value ∧
      s.out.length < (σ.arrs "vm.output").length) append
      (fun _ τ => Represents w { s with pc := s.pc + 1, out := s.out ++ [value % 2 ^ w] } τ ∧
        τ.vars "vm.running" = 1) 17 := by
  rintro σ ⟨⟨hcore, htapes⟩, hrunning, hvalue, hroom⟩
  have hσpc := hcore.2.1
  have hσM := hcore.2.2.1
  have hσout := htapes.2.2.2.2.2
  have hprefix := htapes.2.2.2.2.1
  have happend := prefix_append s.out (σ.arrs "vm.output") (value % 2 ^ w) hprefix hroom
  have hd := (Nat.div_le_self value (2 ^ w)).trans_lt hv
  have hp := (Nat.div_mul_le_self value (2 ^ w)).trans_lt hv
  have hs := (Nat.sub_le value (value / 2 ^ w * 2 ^ w)).trans_lt hv
  simp only [append, remainder, increment]
  run_vcg
  all_goals simp_all [Represents, Core, Tapes, Prefix, RamSparseRead.Representation,
    Nat.mod_def, Nat.mul_comm]

theorem write_spec (B w : ℕ) (s : SparseRam.SparseState) (a : ℕ)
    (h1 : 1 < B) (hM : 2 ^ w < B) (ha : a < B)
    (hwords : SparseBounds.MemoryWords w s.memory) (hpc : s.pc + 1 < B)
    (hmem : s.memory.length < B) (hout : s.out.length + 1 < B) :
    Spec B (fun σ => Represents w s σ ∧ σ.vars "vm.running" = 1 ∧
      s.out.length < (σ.arrs "vm.output").length) (instruction (.write a))
      (fun _ τ => Represents w { s with pc := s.pc + 1, out := s.out ++ [SparseRam.lookup s.memory (a % 2 ^ w) % 2 ^ w] } τ ∧
        τ.vars "vm.running" = 1) (16 * s.memory.length + 35) := by
  let value := SparseRam.lookup s.memory (a % 2 ^ w)
  have hvalue := (SparseBounds.lookup_bound w s.memory (a % 2 ^ w) hwords).trans hM
  have hread := read_literal_spec B w s.pc s.memory a "vm.left" h1 hM ha hmem hwords
    (by decide) (by decide) (by decide) (by decide)
  rintro σ ⟨⟨hcore, htapes⟩, hrunning, hroom⟩
  obtain ⟨ν, hget, hpost⟩ := hread σ hcore
  have htapesν := tapes_frame hget s htapes
    (by simp [RamSparseRead.read, RamSparseMemory.lookup, RamSparseMemory.scanStep, Com.warrs])
    (by simp [RamSparseRead.read, RamSparseMemory.lookup, RamSparseMemory.scanStep, Com.warrs])
    (by simp [RamSparseRead.read, RamSparseMemory.lookup, RamSparseMemory.scanStep, Com.wvars])
    (by simp [RamSparseRead.read, RamSparseMemory.lookup, RamSparseMemory.scanStep, Com.wvars])
    (by simp [RamSparseRead.read, RamSparseMemory.lookup, RamSparseMemory.scanStep, Com.wvars])
  have hrunningν := (hget.frame_var "vm.running" (by simp [RamSparseRead.read,
    RamSparseMemory.lookup, RamSparseMemory.scanStep, Com.wvars])).trans hrunning
  have hroomν : s.out.length < (ν.arrs "vm.output").length := by
    rwa [RamFrames.run_array_length hget "vm.output"]
  obtain ⟨τ, hwrite, hfinal⟩ := append_spec B w s value h1 hM hvalue hpc hout ν
    ⟨⟨hpost.1, htapesν⟩, hrunningν, hpost.2, hroomν⟩
  exact ⟨τ, (hget.seq hwrite).mono (by omega), hfinal⟩

end Lax455465Proofs.RamVirtualOutput
