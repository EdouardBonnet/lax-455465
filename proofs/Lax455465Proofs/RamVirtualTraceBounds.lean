import Lax455465Proofs.RamVirtualInstruction

namespace Lax455465Proofs.RamVirtualTraceBounds

open Lax808846.Ram SparseRam RamVirtualInstruction

/-- Literal bounds are monotone in the available native word range. -/
theorem literals_mono (i : Instr) {A B : ℕ} (h : LiteralsFit A i) (hab : A ≤ B) :
    LiteralsFit B i := by
  cases i <;> simp_all [LiteralsFit] <;> omega

theorem step_input (w : ℕ) (p : Program) (s t : SparseState)
    (h : step w p s = some t) : t.input = s.input := by
  obtain ⟨i, _, he⟩ := Option.bind_eq_some_iff.mp h
  exact SparseBounds.effect_input_eq w i s t he

/-- A successful source step either advances a valid instruction position
or jumps to a fixed literal label. Both stay inside the chosen host range. -/
theorem step_pc (B w : ℕ) (p : Program) (s t : SparseState)
    (hp : p.length + 1 < B) (hlit : ∀ i ∈ p, LiteralsFit (B - 1) i)
    (hs : step w p s = some t) : t.pc + 1 < B := by
  obtain ⟨i, hi, he⟩ := Option.bind_eq_some_iff.mp hs
  have hpos : s.pc < p.length := by
    by_contra h
    rw [List.getElem?_eq_none (by omega)] at hi
    cases hi
  have hilit := hlit i (List.mem_of_getElem? hi)
  have hseq : s.pc + 2 < B := by omega
  cases i <;> simp only [effect] at he
  all_goals first
    | solve | (cases he <;> simp_all [assign, LiteralsFit] <;> omega)
    | solve | (cases he <;> simp_all [assign, LiteralsFit] <;> split_ifs <;> omega)
    | solve | (cases hr : s.inp.head? <;>
        simp only [hr, Option.map_some, Option.map_none] at he <;>
        cases he <;> simp_all [assign, LiteralsFit] <;> omega)

theorem run_pc (B w : ℕ) (p : Program) (s t : SparseState) (k : ℕ)
    (hp : p.length + 1 < B) (hlit : ∀ i ∈ p, LiteralsFit (B - 1) i)
    (hstart : s.pc + 1 < B) (hr : run w p k s = some t) : t.pc + 1 < B := by
  induction k generalizing s with
  | zero => cases hr; exact hstart
  | succ k ih =>
    obtain ⟨u, hs, ht⟩ := Option.bind_eq_some_iff.mp hr
    exact ih u (step_pc B w p s u hp hlit hs) ht

end Lax455465Proofs.RamVirtualTraceBounds
