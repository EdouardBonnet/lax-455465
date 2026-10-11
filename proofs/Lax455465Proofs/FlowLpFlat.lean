import Lax455465Proofs.FlowLpIndices
import Lax109476.RationalEncoding

namespace Lax455465Proofs.FlowLpFlat

open DirectedFlowLP FlowLpIndices

/-- Numerical form of the demand divergence. All inputs are runtime indices. -/
def divergence (weight : ℕ → ℚ) (n commodity vertex : ℕ) : ℚ :=
  if commodity / n = commodity % n then 0 else
    (if vertex = commodity / n then weight (commodity / n) * weight (commodity % n) else 0) -
    (if vertex = commodity % n then weight (commodity / n) * weight (commodity % n) else 0)

def balanceCoefficient (weight : ℕ → ℚ) (n balance column : ℕ) : ℚ :=
  if column = 0 then -divergence weight n (balance / n) (balance % n) else
    if (column - 1) / (n * n) = balance / n then
      (if ((column - 1) % (n * n)) / n = balance % n then 1 else 0) -
      (if ((column - 1) % (n * n)) % n = balance % n then 1 else 0)
    else 0

def coefficient (weight : ℕ → ℚ) (n row column : ℕ) : ℚ :=
  if row < n * n then
    if column = 0 then 0 else if (column - 1) % (n * n) = row then 1 else 0
  else
    let b := balanceCoefficient weight n ((row - n * n) % ((n * n) * n)) column
    if (row - n * n) / ((n * n) * n) = 0 then b else -b

theorem divergence_eq {n : ℕ} (I : Lax455465.RationalEncoding.RationalInstance n)
    (weight : ℕ → ℚ) (hw : ∀ v : Fin n, weight v.val = (I.weight v : ℚ))
    (s t u : Fin n) :
    divergence weight n (edgeIndex n (s,t)).val u.val = DirectedFlowLP.divergence I s t u := by
  simp only [divergence, edge_div, edge_mod, hw, DirectedFlowLP.divergence, Fin.val_inj]

theorem balance_eq {n : ℕ} (I : Lax455465.RationalEncoding.RationalInstance n)
    (weight : ℕ → ℚ) (hw : ∀ v : Fin n, weight v.val = (I.weight v : ℚ))
    (b : Balance n) (v : Variable n) :
    balanceCoefficient weight n (balanceIndex n b).val (variableIndex n v).val =
      DirectedFlowLP.balanceCoefficient I b v := by
  rcases b with ⟨⟨s,t⟩,u⟩
  cases v with
  | inl v =>
    simp only [balanceCoefficient, value_variable, if_true, balance_div, balance_mod,
      divergence_eq I weight hw, DirectedFlowLP.balanceCoefficient]
  | inr a =>
    rcases a with ⟨⟨s',t'⟩,⟨u',v'⟩⟩
    have hcol : (variableIndex n (.inr ((s',t'),(u',v')))).val ≠ 0 := by
      rw [arc_variable]; omega
    simp only [balanceCoefficient, if_neg hcol, arc_div, arc_mod, balance_div, balance_mod,
      edge_div, edge_mod, DirectedFlowLP.balanceCoefficient, Fin.val_inj,
      (edgeIndex n).apply_eq_iff_eq]

theorem coefficient_eq {n : ℕ} (I : Lax455465.RationalEncoding.RationalInstance n)
    (weight : ℕ → ℚ) (hw : ∀ v : Fin n, weight v.val = (I.weight v : ℚ))
    (r : Row n) (v : Variable n) :
    coefficient weight n (rowIndex n r).val (variableIndex n v).val =
      DirectedFlowLP.coefficient I r v := by
  cases r with
  | inl e =>
    rcases e with ⟨u,v₀⟩
    have hrow : (rowIndex n (.inl (u,v₀))).val < n*n := by
      rw [capacity_row, ← edge_value]; exact (edgeIndex n (u,v₀)).isLt
    cases v with
    | inl v => simp only [coefficient, if_pos hrow, value_variable, if_true, DirectedFlowLP.coefficient]
    | inr a =>
      rcases a with ⟨⟨s,t⟩,⟨u',v'⟩⟩
      have hcol : (variableIndex n (.inr ((s,t),(u',v')))).val ≠ 0 := by rw [arc_variable]; omega
      rw [coefficient, if_pos hrow]
      simp only [if_neg hcol, arc_mod,
        show (rowIndex n (.inl (u,v₀))).val = (edgeIndex n (u,v₀)).val by rw [capacity_row,edge_value],
        edge_equal, DirectedFlowLP.coefficient]
  | inr b =>
    rcases b with ⟨sign,⟨⟨s,t⟩,u⟩⟩
    have hrow : ¬(rowIndex n (.inr (sign,((s,t),u)))).val < n*n := by rw [balance_row]; omega
    have hs : sign.val = 0 ↔ sign = 0 := by rw [← Fin.val_inj]; rfl
    simp only [coefficient, if_neg hrow, row_mod, row_div, balance_eq I weight hw,
      DirectedFlowLP.coefficient, hs]

def rowBound (capacity : ℕ → ℚ) (n row : ℕ) : ℚ :=
  if row < n * n then capacity row else 0

def objective (column : ℕ) : ℚ := if column = 0 then 1 else 0

theorem rowBound_eq {n : ℕ} (I : Lax455465.RationalEncoding.RationalInstance n)
    (capacity : ℕ → ℚ) (hc : ∀ u v : Fin n,
      capacity (edgeIndex n (u,v)).val = (I.capacity u v : ℚ)) (r : Row n) :
    rowBound capacity n (rowIndex n r).val = DirectedFlowLP.rowBound I r := by
  cases r with
  | inl e =>
    rcases e with ⟨u,v⟩
    have hrow : (rowIndex n (.inl (u,v))).val < n*n := by
      rw [capacity_row, ← edge_value]; exact (edgeIndex n (u,v)).isLt
    rw [rowBound, if_pos hrow]
    simpa only [capacity_row, ← edge_value, DirectedFlowLP.rowBound] using hc u v
  | inr b =>
    rcases b with ⟨sign,⟨⟨s,t⟩,u⟩⟩
    have hrow : ¬(rowIndex n (.inr (sign,((s,t),u)))).val < n*n := by rw [balance_row]; omega
    simp only [rowBound, if_neg hrow, DirectedFlowLP.rowBound]

theorem objective_eq {n : ℕ} (v : Variable n) :
    objective (variableIndex n v).val = DirectedFlowLP.objective v := by
  cases v with
  | inl v => simp only [objective, value_variable, if_true, DirectedFlowLP.objective]
  | inr a =>
    rcases a with ⟨⟨s,t⟩,⟨u,v⟩⟩
    have hcol : (variableIndex n (.inr ((s,t),(u,v)))).val ≠ 0 := by rw [arc_variable]; omega
    simp only [objective, if_neg hcol, DirectedFlowLP.objective]

/-- The flat runtime formula is exactly the matrix in the mathematical LP. -/
theorem coefficient_at {n : ℕ} (I : Lax455465.RationalEncoding.RationalInstance n)
    (weight : ℕ → ℚ) (hw : ∀ v : Fin n, weight v.val = (I.weight v : ℚ))
    (i : Fin (n*n + 2*((n*n)*n))) (j : Fin (1+(n*n)*(n*n))) :
    coefficient weight n i.val j.val = (program I).A i j := by
  simpa only [program, Equiv.apply_symm_apply] using
    coefficient_eq I weight hw ((rowIndex n).symm i) ((variableIndex n).symm j)

end Lax455465Proofs.FlowLpFlat
