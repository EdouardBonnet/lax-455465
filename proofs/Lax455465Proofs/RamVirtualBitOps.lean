import Lax455465Proofs.RamVirtualStage

namespace Lax455465Proofs.RamVirtualBitOps

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamVirtualCore RamVirtualArithmetic RamVirtualProgram

theorem shift_bound (w value count : ℕ) : SparseRam.shiftValue w value count < 2 ^ w := by
  unfold SparseRam.shiftValue
  split_ifs
  · exact Nat.mod_lt _ (Nat.two_pow_pos w)
  · exact Nat.two_pow_pos w

theorem shift_core_spec (B w pc : ℕ) (m : SparseRam.Memory) (a b c : ℕ)
    (hB : 2 * (2 ^ w) ^ 2 + 3 < B) (ha : a < B) (hb : b < B) (hc : c < B)
    (hwords : SparseBounds.MemoryWords w m) (hpc : pc + 1 < B) (hlen : m.length + 1 < B) :
    Spec B (Working w pc m) (instruction (.shiftl a b c))
      (fun _ τ => Core w (pc + 1) (SparseRam.write w m a
        (SparseRam.lookup m (b % 2 ^ w) * 2 ^ SparseRam.lookup m (c % 2 ^ w))) τ)
      (32 * m.length + 92) := by
  let l := SparseRam.lookup m (b % 2 ^ w)
  let r := SparseRam.lookup m (c % 2 ^ w)
  have h1 : 1 < B := by omega
  have hM : 2 ^ w < B := by nlinarith [Nat.two_pow_pos w]
  have hl := SparseBounds.lookup_bound w m (b % 2 ^ w) hwords
  have hr := SparseBounds.lookup_bound w m (c % 2 ^ w) hwords
  have hshift := RamWordOps.shift_spec B w l r hB hl hr
  have hstage := RamVirtualStage.result_spec B w pc m a (SparseRam.shiftValue w l r)
    RamWordOps.shift 16 _ hshift
    (by simp [RamWordOps.shift, RamWordOps.binary, RamWordOps.reduce, Com.warrs])
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;>
        simp [RamWordOps.shift, RamWordOps.binary, RamWordOps.reduce, Com.wvars])
    h1 hM ha ((shift_bound w l r).trans hM) hpc hlen
  have heq : SparseRam.write w m a (SparseRam.shiftValue w l r) =
      SparseRam.write w m a (l * 2 ^ r) := by
    simp only [SparseRam.shiftValue_eq, SparseRam.write, Nat.mod_mod]
  rw [heq] at hstage
  have hstage' : Spec B (fun σ => Working w pc m σ ∧ σ.vars "vm.left" = l ∧ σ.vars "vm.right" = r)
      (.seq RamWordOps.shift (writeBack (.lit a) (.var "vm.result")))
      (fun _ τ => Core w (pc + 1) (SparseRam.write w m a (l * 2 ^ r)) τ) 56 :=
    hstage.pre (fun _ h => ⟨h.1, h.1.1.2.2.1, h.1.1.2.2.2, h.2.1, h.2.2⟩)
  have h := operands_spec B w pc m b c _ 56 _ h1 hM hb hc (by omega) hwords hstage'
  simpa only [instruction, Nat.add_assoc, Nat.reduceAdd, l, r] using h

theorem complement_bound (w left : ℕ) : 2 ^ w - 1 - left < 2 ^ w := by
  have h := Nat.two_pow_pos w
  omega

theorem not_core_spec (B w pc : ℕ) (m : SparseRam.Memory) (a b : ℕ)
    (h1 : 1 < B) (hM : 2 ^ w < B) (ha : a < B) (hb : b < B)
    (hwords : SparseBounds.MemoryWords w m) (hpc : pc + 1 < B) (hlen : m.length + 1 < B) :
    Spec B (Working w pc m) (instruction (.not a b))
      (fun _ τ => Core w (pc + 1) (SparseRam.write w m a
        (2 ^ w - 1 - SparseRam.lookup m (b % 2 ^ w))) τ) (16 * m.length + 64) := by
  let l := SparseRam.lookup m (b % 2 ^ w)
  have hleft := SparseBounds.lookup_bound w m (b % 2 ^ w) hwords
  have hnot := RamWordOps.complement_spec B w l hM hleft
  have hstage := RamVirtualStage.result_spec B w pc m a (2 ^ w - 1 - l)
    RamWordOps.complement 6 _ hnot
    (by simp [RamWordOps.complement, Com.warrs])
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> simp [RamWordOps.complement, Com.wvars])
    h1 hM ha ((complement_bound w l).trans hM) hpc hlen
  have hstage' : Spec B (fun σ => Working w pc m σ ∧ σ.vars "vm.left" = l)
      (.seq RamWordOps.complement (writeBack (.lit a) (.var "vm.result")))
      (fun _ τ => Core w (pc + 1) (SparseRam.write w m a (2 ^ w - 1 - l)) τ) 46 :=
    hstage.pre (fun _ h => ⟨h.1, h.1.1.2.2.1, h.2⟩)
  have h := operand_spec B w pc m b _ 46 _ h1 hM hb (by omega) hwords hstage'
  simpa only [instruction, Nat.add_assoc, Nat.reduceAdd, l] using h

end Lax455465Proofs.RamVirtualBitOps
