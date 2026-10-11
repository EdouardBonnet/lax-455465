import Lax455465Proofs.SparseRam

namespace Lax455465Proofs.SparseBounds

open Lax808846.Ram SparseRam

def MemoryWords (w : ℕ) (m : Memory) : Prop := ∀ r ∈ m, r.1 < 2 ^ w ∧ r.2 < 2 ^ w

theorem lookup_bound (w : ℕ) (m : Memory) (a : ℕ) (h : MemoryWords w m) :
    lookup m a < 2 ^ w := by
  induction m with
  | nil => exact Nat.two_pow_pos w
  | cons r rest ih =>
    unfold lookup
    split_ifs
    · exact (h r List.mem_cons_self).2
    · exact ih (fun r hr => h r (List.mem_cons_of_mem _ hr))

theorem write_words (w : ℕ) (m : Memory) (a v : ℕ) (h : MemoryWords w m) :
    MemoryWords w (write w m a v) := by
  intro r hr
  rcases List.mem_cons.mp hr with he | ht
  · subst r
    exact ⟨Nat.mod_lt _ (Nat.two_pow_pos w), Nat.mod_lt _ (Nat.two_pow_pos w)⟩
  · exact h r ht

theorem effect_words (w : ℕ) (i : Instr) (s τ : SparseState)
    (hwords : MemoryWords w s.memory) (hs : effect w i s = some τ) : MemoryWords w τ.memory := by
  cases i <;> simp only [effect] at hs
  all_goals first
    | solve | (cases hs <;> exact write_words _ _ _ _ hwords)
    | solve | (cases hs <;> exact hwords)
    | solve | (cases hi : s.inp.head? <;>
      (try simp only [hi, Option.map_some, Option.map_none] at hs) <;>
      cases hs <;> exact write_words _ _ _ _ hwords)

theorem effect_output_le (w : ℕ) (i : Instr) (s τ : SparseState)
    (hs : effect w i s = some τ) : τ.out.length ≤ s.out.length + 1 := by
  cases i <;> simp only [effect] at hs
  all_goals first
    | solve | (cases hs <;> simp [assign])
    | solve | (cases hi : s.inp.head? <;>
      (try simp only [hi, Option.map_some, Option.map_none] at hs) <;>
      cases hs <;> simp [assign])

theorem effect_input_eq (w : ℕ) (i : Instr) (s τ : SparseState)
    (hs : effect w i s = some τ) : τ.input = s.input := by
  cases i <;> simp only [effect] at hs
  all_goals first
    | solve | (cases hs <;> rfl)
    | solve | (cases hi : s.inp.head? <;>
      (try simp only [hi, Option.map_some, Option.map_none] at hs) <;>
      cases hs <;> rfl)

theorem step_words (w : ℕ) (p : Program) (s τ : SparseState)
    (hwords : MemoryWords w s.memory) (hs : step w p s = some τ) : MemoryWords w τ.memory := by
  obtain ⟨i, _, he⟩ := Option.bind_eq_some_iff.mp hs
  exact effect_words w i s τ hwords he

theorem step_output_le (w : ℕ) (p : Program) (s τ : SparseState)
    (hs : step w p s = some τ) : τ.out.length ≤ s.out.length + 1 := by
  obtain ⟨i, _, he⟩ := Option.bind_eq_some_iff.mp hs
  exact effect_output_le w i s τ he

theorem run_words (w : ℕ) (p : Program) (t : ℕ) (s τ : SparseState)
    (hwords : MemoryWords w s.memory) (hs : run w p t s = some τ) : MemoryWords w τ.memory := by
  induction t generalizing s τ with
  | zero => cases hs <;> exact hwords
  | succ t ih =>
    obtain ⟨ν, hstep, hrest⟩ := Option.bind_eq_some_iff.mp hs
    exact ih ν τ (step_words w p s ν hwords hstep) hrest

theorem run_output_le (w : ℕ) (p : Program) (t : ℕ) (s τ : SparseState)
    (hs : run w p t s = some τ) : τ.out.length ≤ s.out.length + t := by
  induction t generalizing s τ with
  | zero => cases hs; omega
  | succ t ih =>
    obtain ⟨ν, hstep, hrest⟩ := Option.bind_eq_some_iff.mp hs
    have hfirst := step_output_le w p s ν hstep
    have hlast := ih ν τ hrest
    omega

end Lax455465Proofs.SparseBounds
