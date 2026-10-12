import Lax455465Proofs.LayeredLpIndices
import Lax109476.RationalEncoding

namespace Lax455465Proofs.LayeredLpFlat
open LayeredFlowLP LayeredLpIndices

abbrev rows (n L : ℕ) := n*n+2*((n*n)*((L+1)*n))
abbrev columns (n L : ℕ) := 1+(n*n)*(L*(n*n))

def arcCommodity (n L j : ℕ) := (j-1)/(L*(n*n))
def arcRest (n L j : ℕ) := (j-1)%(L*(n*n))
def arcLayer (n L j : ℕ) := arcRest n L j/(n*n)
def arcEdge (n L j : ℕ) := arcRest n L j%(n*n)
def arcSource (n L j : ℕ) := arcEdge n L j/n
def arcTarget (n L j : ℕ) := arcEdge n L j%n
def rowSign (n L i : ℕ) := (i-n*n)/((n*n)*((L+1)*n))
def rowBalance (n L i : ℕ) := (i-n*n)%((n*n)*((L+1)*n))
def rowCommodity (n L i : ℕ) := rowBalance n L i/((L+1)*n)
def rowRest (n L i : ℕ) := rowBalance n L i%((L+1)*n)
def rowLayer (n L i : ℕ) := rowRest n L i/n
def rowVertex (n L i : ℕ) := rowRest n L i%n

theorem arc_bounds (n L j : ℕ) :
    arcCommodity n L j ≤ j ∧ arcLayer n L j ≤ j ∧
      arcSource n L j ≤ j ∧ arcTarget n L j ≤ j := by
  have ho : j-1 ≤ j := Nat.sub_le _ _
  have hr : arcRest n L j ≤ j := (Nat.mod_le _ _).trans ho
  have he : arcEdge n L j ≤ j := (Nat.mod_le _ _).trans hr
  exact ⟨(Nat.div_le_self _ _).trans ho,(Nat.div_le_self _ _).trans hr,
    (Nat.div_le_self _ _).trans he,(Nat.mod_le _ _).trans he⟩

theorem row_bounds (n L i : ℕ) :
    rowSign n L i ≤ i ∧ rowCommodity n L i ≤ i ∧ rowLayer n L i ≤ i ∧
      rowVertex n L i ≤ i ∧ rowCommodity n L i/n ≤ i ∧ rowCommodity n L i%n ≤ i := by
  have ho : i-n*n ≤ i := Nat.sub_le _ _
  have hb : rowBalance n L i ≤ i := (Nat.mod_le _ _).trans ho
  have hr : rowRest n L i ≤ i := (Nat.mod_le _ _).trans hb
  have hc : rowCommodity n L i ≤ i := (Nat.div_le_self _ _).trans hb
  exact ⟨(Nat.div_le_self _ _).trans ho,hc,(Nat.div_le_self _ _).trans hr,
    (Nat.mod_le _ _).trans hr,(Nat.div_le_self _ _).trans hc,(Nat.mod_le _ _).trans hc⟩

def incidenceValue (ac rc k j u v z : ℕ) : ℚ :=
  if ac=rc then (if k=j ∧ u=z then 1 else 0)-(if k+1=j ∧ v=z then 1 else 0) else 0

def divergenceValue (n L st j u : ℕ) : ℚ :=
  if st/n=st%n then 0 else
    ((if j=0 ∧ u=st/n then 1 else 0)-(if j=L ∧ u=st%n then 1 else 0))/2

def capacityValue (n i j u v : ℕ) : ℚ :=
  if j=0 then 0 else if i/n=i%n then 0 else
    (if u=i/n ∧ v=i%n then 1 else 0)+(if u=i%n ∧ v=i/n then 1 else 0)

def balanceValue (n L i j : ℕ) : ℚ :=
  if j=0 then -divergenceValue n L (rowCommodity n L i) (rowLayer n L i) (rowVertex n L i)
  else incidenceValue (arcCommodity n L j) (rowCommodity n L i)
    (arcLayer n L j) (rowLayer n L i) (arcSource n L j) (arcTarget n L j) (rowVertex n L i)

/-- Numerical coefficients use only runtime dimensions, quotient/remainder,
and comparisons. All entries belong to {0, ±1, ±1/2}. -/
def coefficient (n L i j : ℕ) : ℚ :=
  if i<n*n then capacityValue n i j (arcSource n L j) (arcTarget n L j)
  else if rowSign n L i=0 then balanceValue n L i j else -balanceValue n L i j

theorem arc_fields {n L : ℕ} (a : Arc n L) :
    arcCommodity n L (variableIndex n L (.inr a)).val=(DirectedFlowLP.edgeIndex n a.1).val ∧
    arcLayer n L (variableIndex n L (.inr a)).val=a.2.1.val ∧
    arcSource n L (variableIndex n L (.inr a)).val=a.2.2.1.val ∧
    arcTarget n L (variableIndex n L (.inr a)).val=a.2.2.2.val := by
  rcases a with ⟨st,k,u,v⟩
  simp [arcCommodity,arcLayer,arcSource,arcTarget,arcEdge,arcRest,
    arc_commodity,arc_rest,arc_layer,arc_edge,FlowLpIndices.edge_div,FlowLpIndices.edge_mod]

theorem row_fields {n L : ℕ} (flag : Fin 2) (b : Balance n L) :
    rowSign n L (rowIndex n L (.inr (flag,b))).val=flag.val ∧
    rowCommodity n L (rowIndex n L (.inr (flag,b))).val=(DirectedFlowLP.edgeIndex n b.1).val ∧
    rowLayer n L (rowIndex n L (.inr (flag,b))).val=b.2.1.val ∧
    rowVertex n L (rowIndex n L (.inr (flag,b))).val=b.2.2.val := by
  simp only [rowSign,rowCommodity,rowLayer,rowVertex,rowRest,rowBalance,
    row_sign,row_balance,balance_commodity,balance_rest,product_div,product_mod,true_and]

theorem divergence_eq {n L : ℕ} (s t : Fin n) (j : Fin (L+1)) (u : Fin n) :
    divergenceValue n L (DirectedFlowLP.edgeIndex n (s,t)).val j.val u.val=
      divergence ((s,t),(j,u)) := by
  have hz : j.val=0 ↔ j=0 := Fin.val_eq_zero_iff
  have hl : j.val=L ↔ j=Fin.last L :=
    show j.val=(Fin.last L).val ↔ j=Fin.last L from Fin.val_inj
  simp only [divergenceValue,FlowLpIndices.edge_div,FlowLpIndices.edge_mod,Fin.val_inj,hz,hl,divergence]
  split_ifs <;> norm_num

theorem incidence_eq {n L : ℕ} (a : Arc n L) (b : Balance n L) :
    incidenceValue (DirectedFlowLP.edgeIndex n a.1).val (DirectedFlowLP.edgeIndex n b.1).val
      a.2.1.val b.2.1.val a.2.2.1.val a.2.2.2.val b.2.2.val=incidence b a := by
  have hk : a.2.1.val=b.2.1.val ↔ a.2.1.castSucc=b.2.1 :=
    show a.2.1.castSucc.val=b.2.1.val ↔ a.2.1.castSucc=b.2.1 from Fin.val_inj
  have hsucc : a.2.1.val+1=b.2.1.val ↔ a.2.1.succ=b.2.1 :=
    show a.2.1.succ.val=b.2.1.val ↔ a.2.1.succ=b.2.1 from Fin.val_inj
  simp only [incidenceValue,FlowLpIndices.edge_equal,hk,hsucc,Fin.val_inj,
    (DirectedFlowLP.edgeIndex n).apply_eq_iff_eq,incidence]

theorem balance_eq {n L : ℕ} (flag : Fin 2) (b : Balance n L) (v : Variable n L) :
    balanceValue n L (rowIndex n L (.inr (flag,b))).val (variableIndex n L v).val=
      balanceCoefficient b v := by
  obtain ⟨_,hst,hj,hu⟩ := row_fields flag b
  cases v with
  | inl v =>
    simp only [balanceValue,value_variable,if_true,hst,hj,hu,balanceCoefficient]
    exact congrArg Neg.neg (divergence_eq b.1.1 b.1.2 b.2.1 b.2.2)
  | inr a =>
    have hv : (variableIndex n L (.inr a)).val ≠ 0 := by rw [arc_variable]; omega
    obtain ⟨ha,hk,hs,ht⟩ := arc_fields a
    simp only [balanceValue,if_neg hv,hst,hj,hu,ha,hk,hs,ht,balanceCoefficient]
    exact incidence_eq a b

theorem coefficient_eq {n L : ℕ} (r : Row n L) (v : Variable n L) :
    coefficient n L (rowIndex n L r).val (variableIndex n L v).val=
      LayeredFlowLP.coefficient r v := by
  cases r with
  | inl e =>
    have hr : (rowIndex n L (.inl e)).val<n*n := by rw [capacity_row]; exact (DirectedFlowLP.edgeIndex n e).isLt
    rw [coefficient,if_pos hr]
    cases v with
    | inl v => simp [capacityValue,value_variable,LayeredFlowLP.coefficient]
    | inr a =>
      have hv : (variableIndex n L (.inr a)).val ≠ 0 := by rw [arc_variable]; omega
      obtain ⟨_,_,hu,hv'⟩ := arc_fields a
      rcases e with ⟨u,v⟩
      simp only [capacityValue,if_neg hv,capacity_row,FlowLpIndices.edge_div,FlowLpIndices.edge_mod,
        hu,hv',Fin.val_inj,LayeredFlowLP.coefficient,usage,Prod.mk.injEq,Prod.ext_iff]
  | inr b =>
    rcases b with ⟨flag,b⟩
    have hr : ¬(rowIndex n L (.inr (flag,b))).val<n*n := by rw [balance_row]; omega
    have hf := (row_fields flag b).1
    have hz : flag.val=0 ↔ flag=0 := Fin.val_eq_zero_iff
    simp only [coefficient,if_neg hr,hf,hz,balance_eq,LayeredFlowLP.coefficient]

theorem coefficient_at {n L : ℕ} (I : Lax455465.RationalEncoding.RationalInstance n)
    (i : Fin (rows n L)) (j : Fin (columns n L)) :
    coefficient n L i.val j.val=(program I L).A i j := by
  simpa only [program,Equiv.apply_symm_apply] using
    coefficient_eq ((rowIndex n L).symm i) ((variableIndex n L).symm j)

end Lax455465Proofs.LayeredLpFlat
