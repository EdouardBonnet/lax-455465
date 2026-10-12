import Lax455465Proofs.LayeredFlowLP
import Lax455465Proofs.FlowLpIndices

namespace Lax455465Proofs.LayeredLpIndices
open LayeredFlowLP

def layerEdgeIndex (n L : ℕ) : Fin L×Edge n ≃ Fin (L*(n*n)) :=
  ((Equiv.refl (Fin L)).prodCongr (DirectedFlowLP.edgeIndex n)).trans finProdFinEquiv

theorem product_div {a b : ℕ} (p : Fin a×Fin b) :
    (finProdFinEquiv p).val/b=p.1.val := by
  have hb : 0 < b := Nat.zero_lt_of_lt p.2.isLt
  simp [finProdFinEquiv,Nat.add_mul_div_left _ _ hb,Nat.div_eq_of_lt p.2.isLt]

theorem product_mod {a b : ℕ} (p : Fin a×Fin b) :
    (finProdFinEquiv p).val%b=p.2.val := by
  simp [finProdFinEquiv,Nat.mod_eq_of_lt p.2.isLt]

theorem value_variable {n L : ℕ} (v : Fin 1) : (variableIndex n L (.inl v)).val=0 := by
  simp [variableIndex,finSumFinEquiv,Equiv.sumCongr]

theorem arc_variable {n L : ℕ} (a : Arc n L) :
    (variableIndex n L (.inr a)).val=1+(arcIndex n L a).val := by
  simp [variableIndex,finSumFinEquiv,Equiv.sumCongr,add_comm]

theorem capacity_row {n L : ℕ} (e : Edge n) :
    (rowIndex n L (.inl e)).val=(DirectedFlowLP.edgeIndex n e).val := by
  simp [rowIndex,finSumFinEquiv,Equiv.sumCongr]

theorem balance_row {n L : ℕ} (flag : Fin 2) (b : Balance n L) :
    (rowIndex n L (.inr (flag,b))).val=n*n+(finProdFinEquiv (flag,balanceIndex n L b)).val := by
  simp [rowIndex,finSumFinEquiv,Equiv.sumCongr,add_comm]

theorem arc_commodity {n L : ℕ} (a : Arc n L) :
    ((variableIndex n L (.inr a)).val-1)/(L*(n*n))=(DirectedFlowLP.edgeIndex n a.1).val := by
  rw [arc_variable,Nat.add_sub_cancel_left]
  exact product_div ((DirectedFlowLP.edgeIndex n a.1),layerEdgeIndex n L a.2)

theorem arc_rest {n L : ℕ} (a : Arc n L) :
    ((variableIndex n L (.inr a)).val-1)%(L*(n*n))=(layerEdgeIndex n L a.2).val := by
  rw [arc_variable,Nat.add_sub_cancel_left]
  exact product_mod ((DirectedFlowLP.edgeIndex n a.1),layerEdgeIndex n L a.2)

theorem arc_layer {n L : ℕ} (a : Fin L×Edge n) :
    (layerEdgeIndex n L a).val/(n*n)=a.1.val := by
  exact product_div (a.1,DirectedFlowLP.edgeIndex n a.2)

theorem arc_edge {n L : ℕ} (a : Fin L×Edge n) :
    (layerEdgeIndex n L a).val%(n*n)=(DirectedFlowLP.edgeIndex n a.2).val := by
  exact product_mod (a.1,DirectedFlowLP.edgeIndex n a.2)

theorem row_sign {n L : ℕ} (flag : Fin 2) (b : Balance n L) :
    ((rowIndex n L (.inr (flag,b))).val-n*n)/((n*n)*((L+1)*n))=flag.val := by
  rw [balance_row,Nat.add_sub_cancel_left]
  exact product_div (flag,balanceIndex n L b)

theorem row_balance {n L : ℕ} (flag : Fin 2) (b : Balance n L) :
    ((rowIndex n L (.inr (flag,b))).val-n*n)%((n*n)*((L+1)*n))=(balanceIndex n L b).val := by
  rw [balance_row,Nat.add_sub_cancel_left]
  exact product_mod (flag,balanceIndex n L b)

theorem balance_commodity {n L : ℕ} (b : Balance n L) :
    (balanceIndex n L b).val/((L+1)*n)=(DirectedFlowLP.edgeIndex n b.1).val := by
  exact product_div (DirectedFlowLP.edgeIndex n b.1,finProdFinEquiv b.2)

theorem balance_rest {n L : ℕ} (b : Balance n L) :
    (balanceIndex n L b).val%((L+1)*n)=(finProdFinEquiv b.2).val := by
  exact product_mod (DirectedFlowLP.edgeIndex n b.1,finProdFinEquiv b.2)

end Lax455465Proofs.LayeredLpIndices
