import Lax455465Proofs.RamVirtualState
import Lax455465Proofs.RamVirtualCore
import Lax455465Proofs.RamFrames

namespace Lax455465Proofs.RamVirtualRead

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamVirtualCore RamVirtualProgram RamVirtualState

def advance : Com := .seq (.assign "vm.result" (.get "vm.input" (.var "vm.cursor")))
  (.assign "vm.cursor" (.add (.var "vm.cursor") (.lit 1)))

/-- A successful sequential read samples exactly the next virtual input
word and advances its cursor by one, preserving the indexed input view. -/
theorem advance_spec (B w : ℕ) (s : SparseRam.SparseState) (value : ℕ) (rest : List ℕ)
    (h1 : 1 < B) (hlen : s.input.length < B) (hwords : ∀ x ∈ s.input, x < B)
    (hread : s.inp = value :: rest) :
    Spec B (fun σ => Represents w s σ ∧ σ.vars "vm.running" = 1) advance
      (fun _ τ => Represents w { s with inp := rest } τ ∧ τ.vars "vm.result" = value ∧
        τ.vars "vm.running" = 1) 7 := by
  rintro σ ⟨⟨hcore, htapes⟩, hrunning⟩
  have hcursor := htapes.2.2.1
  have hpos : σ.vars "vm.cursor" < s.input.length := by
    have hempty := empty_iff_cursor s σ htapes
    have hne : s.inp ≠ [] := by rw [hread]; simp
    exact Nat.lt_of_le_of_ne hcursor (fun he => hne (hempty.mpr he))
  have hdrop : s.input.drop (σ.vars "vm.cursor") =
      s.input[σ.vars "vm.cursor"] :: s.input.drop (σ.vars "vm.cursor" + 1) :=
    List.cons_getElem_drop_succ.symm
  have heq : value :: rest = s.input[σ.vars "vm.cursor"] :: s.input.drop (σ.vars "vm.cursor" + 1) :=
    hread.symm.trans (htapes.2.2.2.1.trans hdrop)
  have hhead := (List.cons.inj heq).1
  have htail := (List.cons.inj heq).2
  have hv : value < B := hhead ▸ hwords s.input[σ.vars "vm.cursor"] (List.getElem_mem hpos)
  have hget : (σ.arrs "vm.input")[σ.vars "vm.cursor"]? = some value := by
    rw [htapes.1 _ hpos, ← hhead]
  have harray : σ.vars "vm.cursor" < (σ.arrs "vm.input").length := by
    by_contra hn
    rw [List.getElem?_eq_none (by omega)] at hget
    cases hget
  clear hdrop heq
  run_vcg
  all_goals simp_all [Represents, Core, Tapes, Prefix, RamSparseRead.Representation]

/-- Exhausted virtual reads halt without changing the represented source
state. The host's input tape has already been copied and is not consulted. -/
theorem empty_spec (B w : ℕ) (s : SparseRam.SparseState) (a : ℕ)
    (hB : 0 < B) (hlen : s.input.length < B) (he : s.inp = []) :
    Spec B (Represents w s) (instruction (.read a))
      (fun _ τ => Represents w s τ ∧ τ.vars "vm.running" = 0) 6 := by
  have hstop := stop_spec B w s hB
  rintro σ ⟨hcore, htapes⟩
  have hcursor := (empty_iff_cursor s σ htapes).mp he
  have hinputlen := htapes.2.1
  obtain ⟨τ, hrun, hpost⟩ := hstop σ ⟨hcore, htapes⟩
  have hbranch : (Cond.lt (.var "vm.cursor") (.var "vm.inputLength")).evalB B σ = some false := by
    rw [evalB_condLt_iff]
    exact ⟨s.input.length, s.input.length,
      by rw [evalB_var_iff]; exact ⟨hcursor.symm, hcursor ▸ hlen⟩,
      by rw [evalB_var_iff]; exact ⟨hinputlen.symm, hinputlen ▸ hlen⟩, by simp⟩
  exact ⟨τ, (Run.ite_false hbranch hrun).mono (by simp [Cond.size, Expr.size]), hpost⟩

/-- The nonempty branch performs the exact sparse read transition, including
its virtual modulo write and the remaining sequential input. -/
theorem nonempty_spec (B w : ℕ) (s : SparseRam.SparseState) (a value : ℕ) (rest : List ℕ)
    (h1 : 1 < B) (hM : 2 ^ w < B) (ha : a < B) (hinput : s.input.length < B)
    (hwords : ∀ x ∈ s.input, x < B) (hread : s.inp = value :: rest)
    (hpc : s.pc + 1 < B) (hmem : s.memory.length + 1 < B) :
    Spec B (fun σ => Represents w s σ ∧ σ.vars "vm.running" = 1 ∧
      s.memory.length < (σ.arrs "vm.addresses").length ∧ s.memory.length < (σ.arrs "vm.values").length)
      (instruction (.read a))
      (fun _ τ => Represents w { SparseRam.assign w s a value with inp := rest } τ ∧
        τ.vars "vm.running" = 1) 51 := by
  rintro σ ⟨⟨hcore, htapes⟩, hrunning, hA, hV⟩
  have hcursor : σ.vars "vm.cursor" < s.input.length := by
    have hempty := empty_iff_cursor s σ htapes
    have hne : s.inp ≠ [] := by rw [hread]; simp
    have hb := htapes.2.2.1
    exact Nat.lt_of_le_of_ne hb (fun he => hne (hempty.mpr he))
  have hv : value < B := by
    apply hwords value
    rw [htapes.2.2.2.1] at hread
    exact List.mem_of_mem_drop (hread ▸ List.mem_cons_self)
  have hadvance := advance_spec B w s value rest h1 hinput hwords hread
  obtain ⟨ν, hadvance, hpost⟩ := hadvance σ ⟨⟨hcore, htapes⟩, hrunning⟩
  have hAν : s.memory.length < (ν.arrs "vm.addresses").length := by
    rwa [RamFrames.run_array_length hadvance "vm.addresses"]
  have hVν : s.memory.length < (ν.arrs "vm.values").length := by
    rwa [RamFrames.run_array_length hadvance "vm.values"]
  obtain ⟨τ, hwrite, hfinal⟩ := writeBack_register_spec B w s.pc s.memory a value h1 hM ha hv hpc hmem
    ν ⟨hpost.1.1, hpost.2.1, hAν, hVν⟩
  have htapesτ := tapes_frame hwrite { s with inp := rest } hpost.1.2
    (by simp [writeBack, RamSparseRead.write, RamSparseMemory.put, increment, Com.warrs])
    (by simp [writeBack, RamSparseRead.write, RamSparseMemory.put, increment, Com.warrs])
    (by simp [writeBack, RamSparseRead.write, RamSparseMemory.put, increment, Com.wvars])
    (by simp [writeBack, RamSparseRead.write, RamSparseMemory.put, increment, Com.wvars])
    (by simp [writeBack, RamSparseRead.write, RamSparseMemory.put, increment, Com.wvars])
  have hrunningτ := (hwrite.frame_var "vm.running" (by simp [writeBack,
    RamSparseRead.write, RamSparseMemory.put, increment, Com.wvars])).trans hpost.2.2
  have hbranch : (Cond.lt (.var "vm.cursor") (.var "vm.inputLength")).evalB B σ = some true := by
    rw [evalB_condLt_iff]
    exact ⟨σ.vars "vm.cursor", s.input.length, evalB_var (hcursor.trans hinput),
      by rw [evalB_var_iff]; exact ⟨htapes.2.1.symm, htapes.2.1 ▸ hinput⟩,
      by simp [hcursor]⟩
  refine ⟨τ, (Run.ite_true hbranch (hadvance.seq hwrite)).mono ?_, ⟨hfinal, htapesτ⟩, hrunningτ⟩
  · simp [Cond.size, Expr.size]

end Lax455465Proofs.RamVirtualRead
