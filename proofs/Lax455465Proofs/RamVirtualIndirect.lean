import Lax455465Proofs.RamVirtualArithmetic

namespace Lax455465Proofs.RamVirtualIndirect

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamVirtualCore RamVirtualArithmetic RamVirtualProgram RamFrames

theorem load_core_spec (B w pc : ℕ) (m : SparseRam.Memory) (a b : ℕ)
    (h1 : 1 < B) (hM : 2 ^ w < B) (ha : a < B) (hb : b < B)
    (hwords : SparseBounds.MemoryWords w m) (hpc : pc + 1 < B) (hlen : m.length + 1 < B) :
    Spec B (Working w pc m) (instruction (.load a b))
      (fun _ τ => Core w (pc + 1) (SparseRam.write w m a
        (SparseRam.lookup m (SparseRam.lookup m (b % 2 ^ w) % 2 ^ w))) τ)
      (32 * m.length + 76) := by
  let address := SparseRam.lookup m (b % 2 ^ w)
  let value := SparseRam.lookup m (address % 2 ^ w)
  have haddress := SparseBounds.lookup_bound w m (b % 2 ^ w) hwords
  have hvalue := (SparseBounds.lookup_bound w m (address % 2 ^ w) hwords).trans hM
  have hread0 := read_expression_spec B w pc m (address % 2 ^ w) "vm.result"
    (remainder (.var "vm.left")) h1 hM
    ((Nat.mod_lt _ (Nat.two_pow_pos w)).trans hM) (by omega) hwords
    (by decide) (by decide) (by decide) (by decide)
  have hread := hread0.mono (show 16 * m.length + (remainder (.var "vm.left")).size + 11 ≤
      16 * m.length + 18 by simp [remainder, Expr.size])
  have hread' := keep_space (keep_space hread "vm.addresses" m.length) "vm.values" m.length
  have hfinish := writeBack_register_spec B w pc m a value h1 hM ha hvalue hpc hlen
  have hbody : Spec B (fun σ => Working w pc m σ ∧ σ.vars "vm.left" = address)
      (.seq (RamSparseRead.read "vm.result" (remainder (.var "vm.left")))
        (writeBack (.lit a) (.var "vm.result")))
      (fun _ τ => Core w (pc + 1) (SparseRam.write w m a value) τ) (16 * m.length + 58) := by
    rintro σ ⟨⟨hcore, hA, hV⟩, hleft⟩
    have he : (remainder (.var "vm.left")).evalB B σ = some (address % 2 ^ w) :=
      evalB_remainder (by rw [evalB_var_iff]; exact ⟨hleft.symm, hleft ▸ haddress.trans hM⟩)
        hcore.2.2.1 hM (haddress.trans hM)
    run_vcg [hread', hfinish]
    all_goals simp_all [value]
  have h := operand_spec B w pc m b _ (16 * m.length + 58) _ h1 hM hb (by omega) hwords hbody
  exact h.mono (by omega)

/-- Stores obtain the destination indirectly before writing the source
value; both reads see the same pre-instruction virtual memory. -/
theorem store_core_spec (B w pc : ℕ) (m : SparseRam.Memory) (a b : ℕ)
    (h1 : 1 < B) (hM : 2 ^ w < B) (ha : a < B) (hb : b < B)
    (hwords : SparseBounds.MemoryWords w m) (hpc : pc + 1 < B) (hlen : m.length + 1 < B) :
    Spec B (Working w pc m) (instruction (.store a b))
      (fun _ τ => Core w (pc + 1) (SparseRam.write w m
        (SparseRam.lookup m (a % 2 ^ w)) (SparseRam.lookup m (b % 2 ^ w))) τ)
      (32 * m.length + 76) := by
  let address := SparseRam.lookup m (a % 2 ^ w)
  let value := SparseRam.lookup m (b % 2 ^ w)
  have haddress := (SparseBounds.lookup_bound w m (a % 2 ^ w) hwords).trans hM
  have hvalue := (SparseBounds.lookup_bound w m (b % 2 ^ w) hwords).trans hM
  have hgetA := read_literal_spec B w pc m a "vm.target" h1 hM ha (by omega) hwords
    (by decide) (by decide) (by decide) (by decide)
  have hgetB := keep_scalar (read_literal_spec B w pc m b "vm.result" h1 hM hb (by omega) hwords
    (by decide) (by decide) (by decide) (by decide)) "vm.target" address
    (by simp [RamSparseRead.read, RamSparseMemory.lookup, RamSparseMemory.scanStep, Com.wvars])
  have hleft := keep_space (keep_space hgetA "vm.addresses" m.length) "vm.values" m.length
  have hright := keep_space (keep_space hgetB "vm.addresses" m.length) "vm.values" m.length
  have hbase := writeBack_general_spec B w pc m address value (.var "vm.target") (.var "vm.result")
    h1 hM haddress hvalue hpc hlen
  have hfinish : Spec B (fun σ => Working w pc m σ ∧ σ.vars "vm.target" = address ∧ σ.vars "vm.result" = value)
      (writeBack (.var "vm.target") (.var "vm.result"))
      (fun _ τ => Core w (pc + 1) (SparseRam.write w m address value) τ) 40 :=
    (hbase.pre (by
      rintro σ ⟨⟨hcore, hA, hV⟩, htarget, hσvalue⟩
      refine ⟨hcore, hA, hV, ?_, ?_⟩
      · rw [evalB_var_iff]
        exact ⟨htarget.symm, htarget ▸ haddress⟩
      · rw [evalB_var_iff]
        simp only [vars_setVar, String.reduceEq, if_false]
        exact ⟨hσvalue.symm, hσvalue ▸ hvalue⟩)).mono (by decide)
  rintro σ ⟨hcore, hA, hV⟩
  simp only [instruction]
  run_vcg [hleft, hright, hfinish]
  all_goals simp_all [Working, address, value]

end Lax455465Proofs.RamVirtualIndirect
