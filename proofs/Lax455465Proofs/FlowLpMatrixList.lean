import Lax455465Proofs.DirectedFlowLP
import Lax109476.RationalEncoding

namespace Lax455465Proofs.FlowLpMatrixList

open Lax109476.LinearProgram

def entry {m n : ℕ} (P : Program ℚ m n) (k : Fin (m*n)) : ℚ :=
  P.A (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2

def values {m n : ℕ} (P : Program ℚ m n) : List ℚ := List.ofFn (entry P)

theorem rowIndex_value {m n : ℕ} (k : Fin (m*n)) :
    (finProdFinEquiv.symm k).1.val = k.val/n := rfl

theorem columnIndex_value {m n : ℕ} (k : Fin (m*n)) :
    (finProdFinEquiv.symm k).2.val = k.val%n := rfl

/-- Flattening the matrix is exactly numerical row-major iteration. -/
theorem values_eq {m n : ℕ} (P : Program ℚ m n) :
    values P = (List.ofFn fun i => List.ofFn (P.A i)).flatten := by
  unfold values
  rw [List.ofFn_mul]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  have hij : i.val*n+j.val < m*n := calc
    _ < (i.val+1)*n := by rw [Nat.add_mul,Nat.one_mul]; exact Nat.add_lt_add_left j.isLt _
    _ ≤ m*n := Nat.mul_le_mul_right _ (Nat.succ_le_iff.mpr i.isLt)
  have hpair : (⟨i.val*n+j.val,hij⟩ : Fin (m*n)) = finProdFinEquiv (i,j) := by
    apply Fin.ext
    simp [finProdFinEquiv]
    ring
  rw [hpair]
  simp only [entry,Equiv.symm_apply_apply]

end Lax455465Proofs.FlowLpMatrixList
