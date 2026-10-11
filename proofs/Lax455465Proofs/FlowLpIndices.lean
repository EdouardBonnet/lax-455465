import Lax455465Proofs.DirectedFlowLP

namespace Lax455465Proofs.FlowLpIndices

open DirectedFlowLP

theorem edge_value {n : ℕ} (s t : Fin n) : (edgeIndex n (s, t)).val = s.val * n + t.val := by
  simp [edgeIndex, finProdFinEquiv]
  ring

theorem arc_value {n : ℕ} (s t u v : Fin n) :
    (arcIndex n ((s, t), (u, v))).val = (s.val * n + t.val) * (n * n) + (u.val * n + v.val) := by
  simp [arcIndex, edgeIndex, finProdFinEquiv]
  ring

theorem balance_value {n : ℕ} (s t u : Fin n) :
    (balanceIndex n ((s, t), u)).val = (s.val * n + t.val) * n + u.val := by
  simp [balanceIndex, edgeIndex, finProdFinEquiv]
  ring

theorem value_variable {n : ℕ} (v : Fin 1) : (variableIndex n (.inl v)).val = 0 := by
  simp [variableIndex, finSumFinEquiv, Equiv.sumCongr]

theorem arc_variable {n : ℕ} (s t u v : Fin n) :
    (variableIndex n (.inr ((s, t), (u, v)))).val =
      1 + (s.val * n + t.val) * (n * n) + (u.val * n + v.val) := by
  simp [variableIndex, arcIndex, edgeIndex, finProdFinEquiv, finSumFinEquiv, Equiv.sumCongr]
  ring

theorem capacity_row {n : ℕ} (u v : Fin n) : (rowIndex n (.inl (u, v))).val = u.val * n + v.val := by
  simp [rowIndex, edgeIndex, finProdFinEquiv, finSumFinEquiv, Equiv.sumCongr]
  ring

theorem balance_row {n : ℕ} (sign : Fin 2) (s t u : Fin n) :
    (rowIndex n (.inr (sign, ((s, t), u)))).val =
      n * n + sign.val * ((n * n) * n) + (s.val * n + t.val) * n + u.val := by
  simp [rowIndex, balanceIndex, edgeIndex, finProdFinEquiv, finSumFinEquiv, Equiv.sumCongr]
  ring

private theorem code_div (a b n : ℕ) (hn : 0 < n) (hb : b < n) :
    (a * n + b) / n = a := by
  rw [Nat.add_comm, Nat.add_mul_div_right b a hn, Nat.div_eq_of_lt hb, Nat.zero_add]

private theorem code_mod (a b n : ℕ) (hb : b < n) : (a * n + b) % n = b := by
  rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hb]

theorem edge_div {n : ℕ} (s t : Fin n) : (edgeIndex n (s, t)).val / n = s.val := by
  rw [edge_value]
  exact code_div _ _ _ ((Nat.zero_le t.val).trans_lt t.isLt) t.isLt

theorem edge_mod {n : ℕ} (s t : Fin n) : (edgeIndex n (s, t)).val % n = t.val := by
  rw [edge_value]
  exact code_mod _ _ _ t.isLt

theorem arc_div {n : ℕ} (s t u v : Fin n) :
    ((variableIndex n (.inr ((s, t), (u, v)))).val - 1) / (n * n) = (edgeIndex n (s, t)).val := by
  have hcol : (variableIndex n (.inr ((s, t), (u, v)))).val - 1 =
      (edgeIndex n (s, t)).val * (n * n) + (edgeIndex n (u, v)).val := by
    rw [arc_variable, edge_value, edge_value]
    omega
  rw [hcol]
  exact code_div _ _ _ (by nlinarith [s.isLt]) (edgeIndex n (u, v)).isLt

theorem arc_mod {n : ℕ} (s t u v : Fin n) :
    ((variableIndex n (.inr ((s, t), (u, v)))).val - 1) % (n * n) = (edgeIndex n (u, v)).val := by
  have hcol : (variableIndex n (.inr ((s, t), (u, v)))).val - 1 =
      (edgeIndex n (s, t)).val * (n * n) + (edgeIndex n (u, v)).val := by
    rw [arc_variable, edge_value, edge_value]
    omega
  rw [hcol]
  exact code_mod _ _ _ (edgeIndex n (u, v)).isLt

theorem balance_div {n : ℕ} (s t u : Fin n) :
    (balanceIndex n ((s, t), u)).val / n = (edgeIndex n (s, t)).val := by
  rw [balance_value, edge_value]
  exact code_div _ _ _ ((Nat.zero_le u.val).trans_lt u.isLt) u.isLt

theorem balance_mod {n : ℕ} (s t u : Fin n) :
    (balanceIndex n ((s, t), u)).val % n = u.val := by
  rw [balance_value]
  exact code_mod _ _ _ u.isLt

theorem row_div {n : ℕ} (sign : Fin 2) (s t u : Fin n) :
    ((rowIndex n (.inr (sign, ((s, t), u)))).val - n * n) / ((n * n) * n) = sign.val := by
  have hrow : (rowIndex n (.inr (sign, ((s, t), u)))).val - n * n =
      sign.val * ((n * n) * n) + (balanceIndex n ((s, t), u)).val := by
    rw [balance_row, balance_value]
    omega
  rw [hrow]
  exact code_div _ _ _ (by nlinarith [s.isLt]) (balanceIndex n ((s, t), u)).isLt

theorem row_mod {n : ℕ} (sign : Fin 2) (s t u : Fin n) :
    ((rowIndex n (.inr (sign, ((s, t), u)))).val - n * n) % ((n * n) * n) =
      (balanceIndex n ((s, t), u)).val := by
  have hrow : (rowIndex n (.inr (sign, ((s, t), u)))).val - n * n =
      sign.val * ((n * n) * n) + (balanceIndex n ((s, t), u)).val := by
    rw [balance_row, balance_value]
    omega
  rw [hrow]
  exact code_mod _ _ _ (balanceIndex n ((s, t), u)).isLt

theorem edge_equal {n : ℕ} (a b : Edge n) :
    (edgeIndex n a).val = (edgeIndex n b).val ↔ a = b := by
  rw [Fin.val_inj]
  exact (edgeIndex n).apply_eq_iff_eq

end Lax455465Proofs.FlowLpIndices
