import Lax455465Proofs.RamVirtualCore
import Lax455465Proofs.RamFrames

namespace Lax455465Proofs.RamVirtualArithmetic

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamVirtualProgram RamVirtualCore RamSparseRead RamFrames

def Working (w pc : ℕ) (m : SparseRam.Memory) (σ : Env) : Prop :=
  Core w pc m σ ∧ m.length < (σ.arrs "vm.addresses").length ∧
    m.length < (σ.arrs "vm.values").length

theorem binary_stage_spec (B w pc : ℕ) (m : SparseRam.Memory) (target left right : ℕ) (op : Bop)
    (h1 : 1 < B) (hM : 2 ^ w < B) (htarget : target < B) (hl : left < B) (hr : right < B)
    (hop : op.apply left right < B) (hpc : pc + 1 < B) (hlen : m.length + 1 < B) :
    Spec B (fun σ => Working w pc m σ ∧ σ.vars "vm.left" = left ∧ σ.vars "vm.right" = right)
      (.seq (RamWordOps.binary op) (writeBack (.lit target) (.var "vm.result")))
      (fun _ τ => Core w (pc + 1) (SparseRam.write w m target (op.apply left right)) τ) 52 := by
  have hbody : Spec B (fun σ => Working w pc m σ ∧ σ.vars "vm.left" = left ∧ σ.vars "vm.right" = right)
      (RamWordOps.binary op) (fun _ τ => Working w pc m τ ∧ τ.vars "vm.result" = op.apply left right % 2 ^ w) 12 := by
    rintro σ ⟨⟨hcore, hA, hV⟩, hleft, hright⟩
    obtain ⟨τ, hrun, hpost⟩ := RamWordOps.binary_spec B (2 ^ w) left right op hM hl hr hop
      σ ⟨hcore.2.2.1, hleft, hright⟩
    have hframe : τ.arrs = σ.arrs := hrun.frame_arrs_eqOn
      (by simp [RamWordOps.binary, RamWordOps.reduce, Com.warrs])
    have hcount := hrun.frame_var "vm.count" (by simp [RamWordOps.binary, RamWordOps.reduce, Com.wvars])
    have hcounter := hrun.frame_var "vm.pc" (by simp [RamWordOps.binary, RamWordOps.reduce, Com.wvars])
    have hmod := hrun.frame_var "vm.modulus" (by simp [RamWordOps.binary, RamWordOps.reduce, Com.wvars])
    have hwidth := hrun.frame_var "vm.width" (by simp [RamWordOps.binary, RamWordOps.reduce, Com.wvars])
    have hcore' : Core w pc m τ := by
      simpa only [Core, Representation, hframe, hcount, hcounter, hmod, hwidth] using hcore
    exact ⟨τ, hrun, ⟨hcore', by simpa only [hframe] using hA, by simpa only [hframe] using hV⟩, hpost⟩
  have hfinish := writeBack_register_spec B w pc m target (op.apply left right % 2 ^ w)
    h1 hM htarget ((Nat.mod_lt _ (Nat.two_pow_pos w)).trans hM) hpc hlen
  have hnormalize : SparseRam.write w m target (op.apply left right % 2 ^ w) =
      SparseRam.write w m target (op.apply left right) := by simp only [SparseRam.write, Nat.mod_mod]
  rw [hnormalize] at hfinish
  rintro σ ⟨⟨hcore, hA, hV⟩, hleft, hright⟩
  run_vcg [hbody, hfinish]
  all_goals simp_all [Working]

theorem operand_spec (B w pc : ℕ) (m : SparseRam.Memory) (address : ℕ)
    (body : Com) (K : ℕ) (Q : Env → Prop)
    (h1 : 1 < B) (hM : 2 ^ w < B) (ha : address < B)
    (hlen : m.length < B) (hwords : SparseBounds.MemoryWords w m)
    (hbody : Spec B (fun σ => Working w pc m σ ∧
      σ.vars "vm.left" = SparseRam.lookup m (address % 2 ^ w)) body (fun _ τ => Q τ) K) :
    Spec B (Working w pc m)
      (.seq (RamSparseRead.read "vm.left" (remainder (.lit address))) body)
      (fun _ τ => Q τ) (16 * m.length + 18 + K) := by
  have hget := read_literal_spec B w pc m address "vm.left" h1 hM ha hlen hwords
    (by decide) (by decide) (by decide) (by decide)
  have hread := keep_space (keep_space hget "vm.addresses" m.length) "vm.values" m.length
  rintro σ ⟨hcore, hA, hV⟩
  run_vcg [hread, hbody]
  all_goals simp_all [Working]

theorem operands_spec (B w pc : ℕ) (m : SparseRam.Memory) (left right : ℕ)
    (body : Com) (K : ℕ) (Q : Env → Prop)
    (h1 : 1 < B) (hM : 2 ^ w < B) (hl : left < B) (hr : right < B)
    (hlen : m.length < B) (hwords : SparseBounds.MemoryWords w m)
    (hbody : Spec B (fun σ => Working w pc m σ ∧
      σ.vars "vm.left" = SparseRam.lookup m (left % 2 ^ w) ∧
      σ.vars "vm.right" = SparseRam.lookup m (right % 2 ^ w)) body (fun _ τ => Q τ) K) :
    Spec B (Working w pc m) (operands left right body) (fun _ τ => Q τ) (32 * m.length + 36 + K) := by
  let l := SparseRam.lookup m (left % 2 ^ w)
  have hgetL := read_literal_spec B w pc m left "vm.left" h1 hM hl hlen hwords
    (by decide) (by decide) (by decide) (by decide)
  have hgetR := keep_scalar (read_literal_spec B w pc m right "vm.right" h1 hM hr hlen hwords
    (by decide) (by decide) (by decide) (by decide)) "vm.left" l
    (by simp [RamSparseRead.read, RamSparseMemory.lookup, RamSparseMemory.scanStep, Com.wvars])
  have hleft := keep_space (keep_space hgetL "vm.addresses" m.length) "vm.values" m.length
  have hright := keep_space (keep_space hgetR "vm.addresses" m.length) "vm.values" m.length
  rintro σ ⟨hcore, hA, hV⟩
  unfold operands
  run_vcg [hleft, hright, hbody]
  all_goals simp_all [Working, l]

theorem binary_spec (B w pc : ℕ) (m : SparseRam.Memory) (target left right : ℕ) (op : Bop)
    (h1 : 1 < B) (hM : 2 ^ w < B) (htarget : target < B) (hl : left < B) (hr : right < B)
    (hwords : SparseBounds.MemoryWords w m)
    (hop : op.apply (SparseRam.lookup m (left % 2 ^ w)) (SparseRam.lookup m (right % 2 ^ w)) < B)
    (hpc : pc + 1 < B) (hlen : m.length + 1 < B) :
    Spec B (Working w pc m) (RamVirtualProgram.binary op target left right)
      (fun _ τ => Core w (pc + 1) (SparseRam.write w m target
        (op.apply (SparseRam.lookup m (left % 2 ^ w)) (SparseRam.lookup m (right % 2 ^ w)))) τ)
      (32 * m.length + 88) := by
  let l := SparseRam.lookup m (left % 2 ^ w)
  let r := SparseRam.lookup m (right % 2 ^ w)
  have hlB : l < B := (SparseBounds.lookup_bound w m _ hwords).trans hM
  have hrB : r < B := (SparseBounds.lookup_bound w m _ hwords).trans hM
  have hgetL := read_literal_spec B w pc m left "vm.left" h1 hM hl (by omega) hwords
    (by decide) (by decide) (by decide) (by decide)
  have hgetR := keep_scalar (read_literal_spec B w pc m right "vm.right" h1 hM hr (by omega) hwords
    (by decide) (by decide) (by decide) (by decide)) "vm.left" l (by simp [RamSparseRead.read, RamSparseMemory.lookup,
      RamSparseMemory.scanStep, Com.wvars])
  have hleft := keep_space (keep_space hgetL "vm.addresses" m.length) "vm.values" m.length
  have hright := keep_space (keep_space hgetR "vm.addresses" m.length) "vm.values" m.length
  have hstage := binary_stage_spec B w pc m target l r op h1 hM htarget hlB hrB hop hpc hlen
  rintro σ ⟨hcore, hA, hV⟩
  simp only [RamVirtualProgram.binary, operands]
  run_vcg [hleft, hright, hstage]
  all_goals simp_all [Working, l, r]

end Lax455465Proofs.RamVirtualArithmetic
