import Lax455465Proofs.RamLayeredData
import Lax455465Proofs.RamFlowUnits
import Lax455465Proofs.RamVectorEncoding
import Lax455465Proofs.LpInputSize
import Lax455465Proofs.FlowLpFlat

namespace Lax455465Proofs.RamLayeredVectors

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamVirtualState LayeredFlowLP LayeredLpIndices LayeredLpFlat
open RamLayeredData
open DirectedFlowLP (edgeIndex)
open scoped NNRat

def bound : Com := .ite (.lt (.var "lp.i") (.var "lp.n2"))
  (RamUnsignedBuffer.read "flow.capacities" "lp.i") RamFractionPrimitives.zero

theorem bound_spec (B M : ℕ) {n L : ℕ} (I : Lax455465.RationalEncoding.RationalInstance n)
    (r : Row n L) (h1 : 1 < B) (hn2 : n*n < B) (hr : (rowIndex n L r).val < B)
    (hcindex : 2*(n*n)+1 < B) (hM : M < B)
    (hnum : ∀ u v, (I.capacity u v).num ≤ M) (hden : ∀ u v, (I.capacity u v).den ≤ M) :
    Spec B (fun σ => Data I L σ ∧ σ.vars "lp.i" = (rowIndex n L r).val) bound
      (fun _ τ => Data I L τ ∧ FractionOutput (rowBound I r) τ) 18 := by
  rintro σ ⟨hdata,hi⟩
  cases r with
  | inl e =>
    rcases e with ⟨u,v⟩
    have he : (rowIndex n L (.inl (u,v))).val = (edgeIndex n (u,v)).val := by rw [capacity_row]
    have hrow : (rowIndex n L (.inl (u,v))).val < n*n := he ▸ (edgeIndex n (u,v)).isLt
    have hcond : (Cond.lt (.var "lp.i") (.var "lp.n2")).evalB B σ = some true := by
      rw [evalB_condLt_iff]
      exact ⟨(rowIndex n L (.inl (u,v))).val,n*n,
        by rw [evalB_var_iff]; exact ⟨hi.symm,hi ▸ hr⟩,
        by rw [evalB_var_iff]; exact ⟨hdata.square.symm,hdata.square ▸ hn2⟩,by simp [hrow]⟩
    have hlen : (RamFlowData.capacities I).length = n*n := by simp [RamFlowData.capacities]
    have hlt : (rowIndex n L (.inl (u,v))).val < (RamFlowData.capacities I).length := by rwa [hlen]
    have hvalue : (RamFlowData.capacities I)[(rowIndex n L (.inl (u,v))).val] = I.capacity u v := by
      simp only [RamFlowData.capacities,List.getElem_ofFn,he,Fin.eta,Equiv.symm_apply_apply]
    obtain ⟨τ,hrun,hpost⟩ := RamUnsignedBuffer.read_spec B "flow.capacities" "lp.i" (RamFlowData.capacities I)
      (rowIndex n L (.inl (u,v))).val hlt (by omega) (by omega)
      (by rw [hvalue]; exact (hnum u v).trans_lt hM)
      (by rw [hvalue]; exact (hden u v).trans_lt hM) (by decide) σ ⟨hdata.capacities,hi⟩
    have hdτ := RamLayeredData.frame hrun I L hdata (by decide) (by decide)
    exact ⟨τ,(Run.ite_true hcond hrun).mono (by simp [Cond.size,Expr.size]),hdτ,
      by simpa only [hvalue,rowBound] using hpost.1⟩
  | inr b =>
    rcases b with ⟨flag,⟨⟨s,t⟩,k,u⟩⟩
    have hrow : ¬(rowIndex n L (.inr (flag,((s,t),(k,u))))).val < n*n := by rw [balance_row]; omega
    have hcond : (Cond.lt (.var "lp.i") (.var "lp.n2")).evalB B σ = some false := by
      rw [evalB_condLt_iff]
      exact ⟨(rowIndex n L (.inr (flag,((s,t),(k,u))))).val,n*n,
        by rw [evalB_var_iff]; exact ⟨hi.symm,hi ▸ hr⟩,
        by rw [evalB_var_iff]; exact ⟨hdata.square.symm,hdata.square ▸ hn2⟩,by simp [hrow]⟩
    obtain ⟨τ,hrun,hpost⟩ := RamFractionPrimitives.zero_spec B h1 σ True.intro
    exact ⟨τ,(Run.ite_false hcond hrun).mono (by simp [Cond.size,Expr.size]),
      RamLayeredData.frame hrun I L hdata (by decide) (by decide),hpost⟩

def objective : Com := RamFlowUnits.objective

theorem objective_spec (B : ℕ) {n L : ℕ} (I : Lax455465.RationalEncoding.RationalInstance n)
    (v : Variable n L) (h1 : 1 < B) (hv : (variableIndex n L v).val < B) :
    Spec B (fun σ => Data I L σ ∧ σ.vars "lp.j" = (variableIndex n L v).val) objective
      (fun _ τ => Data I L τ ∧ FractionOutput (LayeredFlowLP.objective v) τ) 10 := by
  rintro σ ⟨hdata,hj⟩
  obtain ⟨τ,hrun,hpost⟩ := RamFlowUnits.objective_spec B (variableIndex n L v).val h1 hv σ hj
  change FractionOutput (FlowLpFlat.objective (variableIndex n L v).val) τ at hpost
  have he : FlowLpFlat.objective (variableIndex n L v).val=LayeredFlowLP.objective v := by
    cases v with
    | inl i => simp [FlowLpFlat.objective,value_variable,LayeredFlowLP.objective]
    | inr a => simp [FlowLpFlat.objective,arc_variable,LayeredFlowLP.objective]
  rw [he] at hpost
  exact ⟨τ,hrun,RamLayeredData.frame hrun I L hdata (by decide) (by decide),hpost⟩

def bounds : Com := RamVectorEncoding.command "lp.i" "lp.rows" bound

def objectives : Com := RamVectorEncoding.command "lp.j" "lp.columns" objective

/-- Emit all capacity bounds and the zeros for conservation rows. -/
theorem bounds_spec (B M : ℕ) {n L : ℕ} (I : Lax455465.RationalEncoding.RationalInstance n)
    (words : List ℕ) (h1 : 1 < B) (hn2 : n*n < B) (hr : rows n L < B)
    (hcindex : 2*(n*n)+1 < B) (hMpos : 1 ≤ M) (hM : M < B)
    (hlen : words.length+3*rows n L+3 < B)
    (hnum : ∀ u v, (I.capacity u v).num ≤ M) (hden : ∀ u v, (I.capacity u v).den ≤ M) :
    Spec B (fun σ => Data I L σ ∧ Prefix words "lp.word" σ ∧ σ.vars "lp.position" = words.length ∧
      words.length+3*rows n L < (σ.arrs "lp.word").length) bounds
      (fun _ τ => Data I L τ ∧ Prefix (words ++ Lax109476.RationalEncoding.encodeVector (program I L).b) "lp.word" τ ∧
        τ.vars "lp.position" = words.length+3*rows n L) (53*rows n L+6) := by
  let qs := List.ofFn (program I L).b
  have hlength : qs.length = rows n L := by simp [qs]
  have hheight : ∀ i, ∀ hi : i < qs.length, LpInputSize.Height M qs[i] := by
    intro i hi
    have hi' : i < rows n L := by rwa [hlength] at hi
    change LpInputSize.Height M ((List.ofFn (program I L).b)[i])
    simp only [List.getElem_ofFn,program]
    cases (rowIndex n L).symm ⟨i,hi'⟩ with
    | inl e =>
      exact ⟨by simpa only [rowBound,NNRat.natAbs_num_coe] using hnum e.1 e.2,
        by simpa only [rowBound,NNRat.den_coe] using hden e.1 e.2⟩
    | inr b => exact LpInputSize.height_zero hMpos
  have hloop := RamVectorEncoding.command_spec B 18 (Data I L) "lp.i" "lp.rows" qs words bound h1
    (by simpa only [hlength] using hlen)
    (fun i hi => (hheight i hi).1.trans_lt hM) (fun i hi => (hheight i hi).2.trans_lt hM)
    (fun σ h => by simpa only [hlength] using h.rowCount)
    (fun σ k h => RamLayeredData.set_index I L σ "lp.i" k h (by decide))
    (fun i hi => by
      have hi' : i < rows n L := by rwa [hlength] at hi
      simpa only [qs,List.getElem_ofFn,program,Equiv.apply_symm_apply] using
        bound_spec B M I ((rowIndex n L).symm ⟨i,hi'⟩) h1 hn2
          (by simpa only [Equiv.apply_symm_apply] using hi'.trans hr) hcindex hM hnum hden)
    (by decide) (by decide) (by decide) (by decide)
    (fun hrun h => RamLayeredData.frame hrun I L h (by decide) (by decide)) (by decide)
  simpa only [bounds,hlength,qs,RamVectorEncoding.encode,Lax109476.RationalEncoding.encodeVector,
    Nat.reduceAdd] using hloop

/-- Emit the single flow-value objective coefficient and all arc zeros. -/
theorem objectives_spec (B : ℕ) {n L : ℕ} (I : Lax455465.RationalEncoding.RationalInstance n)
    (words : List ℕ) (h1 : 1 < B) (hc : columns n L < B)
    (hlen : words.length+3*columns n L+3 < B) :
    Spec B (fun σ => Data I L σ ∧ Prefix words "lp.word" σ ∧ σ.vars "lp.position" = words.length ∧
      words.length+3*columns n L < (σ.arrs "lp.word").length) objectives
      (fun _ τ => Data I L τ ∧ Prefix (words ++ Lax109476.RationalEncoding.encodeVector (program I L).c) "lp.word" τ ∧
        τ.vars "lp.position" = words.length+3*columns n L) (45*columns n L+6) := by
  let qs := List.ofFn (program I L).c
  have hlength : qs.length = columns n L := by simp [qs]
  have hheight : ∀ i, ∀ hi : i < qs.length, LpInputSize.Height 1 qs[i] := by
    intro i hi
    have hi' : i < columns n L := by rwa [hlength] at hi
    change LpInputSize.Height 1 ((List.ofFn (program I L).c)[i])
    simp only [List.getElem_ofFn,program]
    cases (variableIndex n L).symm ⟨i,hi'⟩ with
    | inl v => exact LpInputSize.height_one (by rfl)
    | inr a => exact LpInputSize.height_zero (by rfl)
  have hloop := RamVectorEncoding.command_spec B 10 (Data I L) "lp.j" "lp.columns" qs words objective h1
    (by simpa only [hlength] using hlen)
    (fun i hi => (hheight i hi).1.trans_lt h1) (fun i hi => (hheight i hi).2.trans_lt h1)
    (fun σ h => by simpa only [hlength] using h.columnCount)
    (fun σ k h => RamLayeredData.set_index I L σ "lp.j" k h (by decide))
    (fun i hi => by
      have hi' : i < columns n L := by rwa [hlength] at hi
      simpa only [qs,List.getElem_ofFn,program,Equiv.apply_symm_apply] using
        objective_spec B I ((variableIndex n L).symm ⟨i,hi'⟩) h1
          (by simpa only [Equiv.apply_symm_apply] using hi'.trans hc))
    (by decide) (by decide) (by decide) (by decide)
    (fun hrun h => RamLayeredData.frame hrun I L h (by decide) (by decide)) (by decide)
  simpa only [objectives,hlength,qs,RamVectorEncoding.encode,Lax109476.RationalEncoding.encodeVector,
    Nat.reduceAdd] using hloop

end Lax455465Proofs.RamLayeredVectors
