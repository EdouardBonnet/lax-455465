import Lax455465Proofs.RamVirtualConstants

namespace Lax455465Proofs.SparseClock
open SparseRam

def next (w : ℕ) (p : Lax808846.Ram.Program) (s : SparseState) : SparseState := (step w p s).getD s

def run (w : ℕ) (p : Lax808846.Ram.Program) : ℕ → SparseState → SparseState
  | 0,s => s
  | k+1,s => run w p k (next w p s)

theorem next_memory (w : ℕ) (p : Lax808846.Ram.Program) (s : SparseState) :
    (next w p s).memory.length ≤ s.memory.length+1 := by
  unfold next
  cases he : step w p s with
  | none => simp
  | some t => exact SparseRam.step_memory_le w p s t he

theorem next_output (w : ℕ) (p : Lax808846.Ram.Program) (s : SparseState) :
    (next w p s).out.length ≤ s.out.length+1 := by
  unfold next
  cases he : step w p s with
  | none => simp
  | some t => exact SparseBounds.step_output_le w p s t he

theorem next_words (w : ℕ) (p : Lax808846.Ram.Program) (s : SparseState)
    (h : SparseBounds.MemoryWords w s.memory) : SparseBounds.MemoryWords w (next w p s).memory := by
  unfold next
  cases he : step w p s with
  | none => exact h
  | some t => exact SparseBounds.step_words w p s t h he

theorem next_input (w : ℕ) (p : Lax808846.Ram.Program) (s : SparseState) : (next w p s).input=s.input := by
  unfold next
  cases he : step w p s with
  | none => rfl
  | some t => exact RamVirtualTraceBounds.step_input w p s t he

theorem next_pc (B w : ℕ) (p : Lax808846.Ram.Program) (s : SparseState)
    (hp : p.length+1 < B) (hlit : ∀ i∈p,RamVirtualInstruction.LiteralsFit (B-1) i)
    (hpc : s.pc+1 < B) : (next w p s).pc+1 < B := by
  unfold next
  cases he : step w p s with
  | none => exact hpc
  | some t => exact RamVirtualTraceBounds.step_pc B w p s t hp hlit he

theorem run_add (w : ℕ) (p : Lax808846.Ram.Program) (a b : ℕ) (s : SparseState) :
    run w p (a+b) s=run w p b (run w p a s) := by
  induction a generalizing s with
  | zero => simp only [Nat.zero_add,run]
  | succ a ih => simpa only [Nat.succ_add,run] using ih (next w p s)

theorem run_of_trace (w : ℕ) (p : Lax808846.Ram.Program) (k : ℕ) (s t : SparseState)
    (hr : SparseRam.run w p k s=some t) : run w p k s=t := by
  induction k generalizing s with
  | zero => exact Option.some.inj hr
  | succ k ih =>
    obtain ⟨u,hs,ht⟩ := Option.bind_eq_some_iff.mp hr
    simpa only [run,next,hs,Option.getD_some] using ih u ht

theorem run_halted (w : ℕ) (p : Lax808846.Ram.Program) (k : ℕ) (s : SparseState)
    (hs : step w p s=none) : run w p k s=s := by
  induction k with
  | zero => rfl
  | succ k ih => simpa only [run,next,hs,Option.getD_none] using ih

/-- The clock can truncate malformed or nonterminating computations. Every
successful execution within its allowance keeps exactly its original output. -/
theorem agrees (w : ℕ) (p : Lax808846.Ram.Program) (k N : ℕ) (s t : SparseState)
    (hk : k ≤ N) (hr : SparseRam.run w p k s=some t) (ht : step w p t=none) : run w p N s=t := by
  rw [show N=k+(N-k) by omega,run_add,run_of_trace w p k s t hr]
  exact run_halted w p (N-k) t ht


def OutputWords (w : ℕ) (s : SparseState) : Prop := ∀ a∈s.out,a < 2^w

theorem effect_output_words (w : ℕ) (i : Lax808846.Ram.Instr) (s t : SparseState)
    (h : OutputWords w s) (hr : effect w i s=some t) : OutputWords w t := by
  cases i <;> simp only [effect] at hr
  all_goals try solve | (cases hr; exact h)
  all_goals try solve | (cases he : s.inp.head? <;>
    simp only [he,Option.map_none,Option.map_some] at hr <;> cases hr; exact h)
  all_goals cases hr
  all_goals
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact h a ha
    · simp only [List.mem_singleton] at ha
      subst a
      exact Nat.mod_lt _ (Nat.two_pow_pos w)

theorem next_output_words (w : ℕ) (p : Lax808846.Ram.Program) (s : SparseState)
    (h : OutputWords w s) : OutputWords w (next w p s) := by
  cases he : step w p s with
  | none => simpa only [next,he,Option.getD_none] using h
  | some t =>
    obtain ⟨i,_,hi⟩ := Option.bind_eq_some_iff.mp he
    simpa only [next,he,Option.getD_some] using effect_output_words w i s t h hi

theorem run_output_words (w : ℕ) (p : Lax808846.Ram.Program) (k : ℕ) (s : SparseState)
    (h : OutputWords w s) : OutputWords w (run w p k s) := by
  induction k generalizing s with
  | zero => exact h
  | succ k ih => exact ih (next w p s) (next_output_words w p s h)

theorem run_output_length (w : ℕ) (p : Lax808846.Ram.Program) (k : ℕ) (s : SparseState) :
    (run w p k s).out.length ≤ s.out.length+k := by
  induction k generalizing s with
  | zero => exact Nat.le_refl _
  | succ k ih =>
    have hi := ih (next w p s)
    have hn := next_output w p s
    dsimp only [run]
    omega

end Lax455465Proofs.SparseClock
