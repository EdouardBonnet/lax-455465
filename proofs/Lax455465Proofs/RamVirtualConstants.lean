import Lax455465Proofs.RamVirtualTraceBounds

namespace Lax455465Proofs.RamVirtualConstants

open Lax808846.Ram RamVirtualInstruction RamVirtualTraceBounds

/-- Fixed literal allowance is part of the fixed program, never a
runtime input or an initialized-memory assumption. -/
def literalBound : Instr → ℕ
  | .set a v => max a v + 2
  | .load a b | .store a b | .not a b | .inputLoad a b => max a b + 2
  | .add a b c | .sub a b c | .mul a b c | .div a b c | .and a b c | .shiftl a b c =>
      max a (max b c) + 2
  | .jzero a l => max a l + 2
  | .jump l | .jeof l => l + 2
  | .inputLength a | .read a | .write a => a + 2
  | .halt => 2

theorem literal_fits (i : Instr) : LiteralsFit (literalBound i - 1) i := by
  cases i <;> simp [LiteralsFit, literalBound]

def allowance (p : Program) : ℕ := p.length + 2 + (p.map literalBound).sum

theorem length_bound (p : Program) : p.length + 1 < allowance p := by
  unfold allowance
  omega

theorem literals_fit (p : Program) : ∀ i ∈ p, LiteralsFit (allowance p - 1) i := by
  intro i hi
  have hsum : literalBound i ≤ (p.map literalBound).sum := List.single_le_sum
    (fun j hj => Nat.zero_le _) (literalBound i) (List.mem_map.mpr ⟨i, hi, rfl⟩)
  exact literals_mono i (literal_fits i) (by unfold allowance; omega)

end Lax455465Proofs.RamVirtualConstants
