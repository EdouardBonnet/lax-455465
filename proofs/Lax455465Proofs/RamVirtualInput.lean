import Lax455465Proofs.RamVirtualStage
import Lax455465Proofs.RamVirtualState

namespace Lax455465Proofs.RamVirtualInput

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamVirtualCore RamVirtualArithmetic RamVirtualProgram RamVirtualState RamFrames

def indexed : Com := .ite (.lt (.var "vm.left") (.var "vm.inputLength"))
  (.assign "vm.result" (.get "vm.input" (.var "vm.left"))) (.assign "vm.result" (.lit 0))

/-- Indexed virtual input preserves the zero default beyond the logical
input length, even when the reserved host array is larger. -/
theorem indexed_spec (B index : ℕ) (input : List ℕ) (hiB : index < B)
    (hlen : input.length < B) (hwords : ∀ x ∈ input, x < B) :
    Spec B (fun σ => σ.vars "vm.left" = index ∧ σ.vars "vm.inputLength" = input.length ∧
      Prefix input "vm.input" σ) indexed
      (fun _ τ => τ.vars "vm.result" = input[index]?.getD 0) 7 := by
  rintro σ ⟨hindex, hlength, hprefix⟩
  have h0 : 0 < B := by omega
  by_cases hi : index < input.length
  · have hget := hprefix index hi
    have hv := hwords input[index] (List.getElem_mem hi)
    have harray : index < (σ.arrs "vm.input").length := by
      by_contra hn
      rw [List.getElem?_eq_none (by omega)] at hget
      cases hget
    run_vcg
    all_goals simp_all
  · have hget : input[index]? = none := List.getElem?_eq_none (by omega)
    run_vcg
    all_goals simp_all <;> omega

/-- Source inputLength writes the length of the virtual physical input,
reduced at the virtual word width, not the remaining sequential length. -/
theorem length_core_spec (B w pc : ℕ) (m : SparseRam.Memory) (inputLength a : ℕ)
    (h1 : 1 < B) (hM : 2 ^ w < B) (ha : a < B) (hinput : inputLength < B)
    (hpc : pc + 1 < B) (hlen : m.length + 1 < B) :
    Spec B (fun σ => Working w pc m σ ∧ σ.vars "vm.inputLength" = inputLength)
      (instruction (.inputLength a))
      (fun _ τ => Core w (pc + 1) (SparseRam.write w m a inputLength) τ) 40 := by
  have hbase := writeBack_general_spec B w pc m a inputLength (.lit a) (.var "vm.inputLength")
    h1 hM ha hinput hpc hlen
  apply (hbase.pre ?_).mono (by simp [Expr.size])
  rintro σ ⟨⟨hcore, hA, hV⟩, hσlen⟩
  refine ⟨hcore, hA, hV, evalB_lit ha, ?_⟩
  rw [evalB_var_iff]
  simp only [vars_setVar, String.reduceEq, if_false]
  exact ⟨hσlen.symm, hσlen ▸ hinput⟩

theorem load_core_spec (B w pc : ℕ) (m : SparseRam.Memory) (input : List ℕ) (a b : ℕ)
    (h1 : 1 < B) (hM : 2 ^ w < B) (ha : a < B) (hb : b < B)
    (hinput : input.length < B) (hinputWords : ∀ x ∈ input, x < B)
    (hwords : SparseBounds.MemoryWords w m) (hpc : pc + 1 < B) (hlen : m.length + 1 < B) :
    Spec B (fun σ => Working w pc m σ ∧ Prefix input "vm.input" σ ∧ σ.vars "vm.inputLength" = input.length)
      (instruction (.inputLoad a b))
      (fun _ τ => Core w (pc + 1) (SparseRam.write w m a
        (input[SparseRam.lookup m (b % 2 ^ w) % 2 ^ w]?.getD 0)) τ) (16 * m.length + 65) := by
  let index := SparseRam.lookup m (b % 2 ^ w)
  have hi := SparseBounds.lookup_bound w m (b % 2 ^ w) hwords
  have hiB := hi.trans hM
  have hvalue : input[index]?.getD 0 < B := by
    by_cases hindex : index < input.length
    · simpa only [List.getElem?_eq_getElem hindex, Option.getD_some] using
        hinputWords input[index] (List.getElem_mem hindex)
    · simp only [List.getElem?_eq_none (by omega : input.length ≤ index), Option.getD_none]
      omega
  have hindexed := indexed_spec B index input hiB hinput hinputWords
  have hbase := RamVirtualStage.result_spec B w pc m a (input[index]?.getD 0) indexed 7 _ hindexed
    (by simp [indexed, Com.warrs])
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> simp [indexed, Com.wvars])
    h1 hM ha hvalue hpc hlen
  have hget := read_literal_spec B w pc m b "vm.left" h1 hM hb (by omega) hwords
    (by decide) (by decide) (by decide) (by decide)
  have hread := keep_space (keep_space hget "vm.addresses" m.length) "vm.values" m.length
  -- Preserve the input metadata and initialized input prefix through the virtual memory read.
  rintro σ ⟨⟨hcore, hA, hV⟩, hprefix, hlength⟩
  obtain ⟨ν, hr, hpost⟩ := hread σ ⟨⟨hcore, hA⟩, hV⟩
  have hinputArr := hr.frame_arr "vm.input" (by simp [RamSparseRead.read,
    RamSparseMemory.lookup, RamSparseMemory.scanStep, Com.warrs])
  have hinputLen := hr.frame_var "vm.inputLength" (by simp [RamSparseRead.read,
    RamSparseMemory.lookup, RamSparseMemory.scanStep, Com.wvars])
  have hpν : Prefix input "vm.input" ν := by simpa only [Prefix, hinputArr] using hprefix
  have hlν : ν.vars "vm.inputLength" = input.length := hinputLen.trans hlength
  obtain ⟨τ, hstage, hfinal⟩ := hbase ν ⟨⟨hpost.1.1.1, hpost.1.2, hpost.2⟩,
    hpost.1.1.2, hlν, hpν⟩
  refine ⟨τ, (hr.seq hstage).mono ?_, ?_⟩
  · omega
  · simpa only [instruction, indexed, index, Nat.mod_eq_of_lt hi] using hfinal

end Lax455465Proofs.RamVirtualInput
