import Lax455465Proofs.RamFlowBalance
import Lax455465Proofs.RamFlowContext
import Lax455465Proofs.RamFlowIndices

namespace Lax455465Proofs.RamFlowCoefficient

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamVirtualState DirectedFlowLP FlowLpIndices
open RamFlowContext
open scoped NNRat

def prepare : Com := .seq RamFlowIndices.column RamFlowIndices.row

def Prepared (n i j : ℕ) (weights : List ℚ≥0) (σ : Env) : Prop :=
  Context n i j weights σ ∧
    σ.vars "lp.arcCommodity" = (j-1)/(n*n) ∧ σ.vars "lp.arc" = (j-1)%(n*n) ∧
    σ.vars "lp.arcSource" = ((j-1)%(n*n))/n ∧ σ.vars "lp.arcTarget" = ((j-1)%(n*n))%n ∧
    σ.vars "lp.sign" = (i-n*n)/((n*n)*n) ∧ σ.vars "lp.balance" = (i-n*n)%((n*n)*n) ∧
    σ.vars "lp.commodity" = ((i-n*n)%((n*n)*n))/n ∧ σ.vars "lp.u" = ((i-n*n)%((n*n)*n))%n ∧
    σ.vars "lp.s" = (((i-n*n)%((n*n)*n))/n)/n ∧ σ.vars "lp.t" = (((i-n*n)%((n*n)*n))/n)%n

theorem prepare_spec (B n i j : ℕ) (weights : List ℚ≥0) (h1 : 1 < B)
    (hn : n < B) (hn2 : n*n < B) (hn3 : (n*n)*n < B) (hi : i < B) (hj : j < B) :
    Spec B (Context n i j weights) prepare (fun _ τ => Prepared n i j weights τ) 58 := by
  rintro σ hctx
  obtain ⟨ν,hcol,hcolPost⟩ := RamFlowIndices.column_spec B n (n*n) j h1 hn hn2 hj σ
    ⟨hctx.1,hctx.2.1,hctx.2.2.2.2.1⟩
  have hctxν := frame hcol n i j weights hctx (by decide) (by decide)
  obtain ⟨τ,hrow,hrowPost⟩ := RamFlowIndices.row_spec B n (n*n) ((n*n)*n) i hn hn2 hn3 hi ν
    ⟨hctxν.1,hctxν.2.1,hctxν.2.2.1,hctxν.2.2.2.1⟩
  have hctxτ := frame hrow n i j weights hctxν (by decide) (by decide)
  have hca := (hrow.frame_var "lp.arcCommodity" (by decide)).trans hcolPost.1
  have hcar := (hrow.frame_var "lp.arc" (by decide)).trans hcolPost.2.1
  have hcas := (hrow.frame_var "lp.arcSource" (by decide)).trans hcolPost.2.2.1
  have hcat := (hrow.frame_var "lp.arcTarget" (by decide)).trans hcolPost.2.2.2
  exact ⟨τ,hcol.seq hrow,hctxτ,hca,hcar,hcas,hcat,hrowPost⟩

/-- One fixed native coefficient command covers capacity rows and both
signs of every conservation row. Dimensions and indices are runtime data. -/
def command : Com := .seq prepare (.ite (.lt (.var "lp.i") (.var "lp.n2")) RamFlowUnits.capacity
  (.seq RamFlowBalance.command RamFlowUnits.rowSign))

theorem command_spec (B M : ℕ) {n : ℕ} (I : Lax455465.RationalEncoding.RationalInstance n)
    (r : Row n) (v : Variable n) (hB : 2*M^2+3 < B)
    (hni : 2*n+1 < B) (hn2 : n*n < B) (hn3 : (n*n)*n < B)
    (hr : (rowIndex n r).val < B) (hv : (variableIndex n v).val < B)
    (hnum : ∀ z, (I.weight z).num ≤ M) (hden : ∀ z, (I.weight z).den ≤ M) :
    Spec B (Context n (rowIndex n r).val (variableIndex n v).val (List.ofFn I.weight)) command
      (fun _ τ => FractionOutput (DirectedFlowLP.coefficient I r v) τ) (36*(M*M).size+194) := by
  have h1 : 1 < B := by nlinarith
  have hn : n < B := by omega
  rintro σ hctx
  obtain ⟨ν,hprep,hprepared⟩ := prepare_spec B n (rowIndex n r).val (variableIndex n v).val
    (List.ofFn I.weight) h1 hn hn2 hn3 hr hv σ hctx
  have hctxν := hprepared.1
  rcases hprepared.2 with ⟨hac,harc,has,hat,hflag,hbal,hcom,hu,hs,ht⟩
  cases r with
  | inl e =>
    rcases e with ⟨a,b⟩
    have hi : (rowIndex n (.inl (a,b))).val < n*n := by
      rw [capacity_row,←edge_value]; exact (edgeIndex n (a,b)).isLt
    have hcond : (Cond.lt (.var "lp.i") (.var "lp.n2")).evalB B ν = some true := by
      rw [evalB_condLt_iff]
      exact ⟨(rowIndex n (.inl (a,b))).val,n*n,
        by rw [evalB_var_iff]; exact ⟨hctxν.2.2.2.1.symm,hctxν.2.2.2.1 ▸ hr⟩,
        by rw [evalB_var_iff]; exact ⟨hctxν.2.1.symm,hctxν.2.1 ▸ hn2⟩,by simp [hi]⟩
    have hcarB : ((variableIndex n v).val-1)%(n*n) < B :=
      (Nat.mod_le _ _).trans_lt ((Nat.sub_le _ _).trans_lt hv)
    obtain ⟨τ,hcap,hpost⟩ := RamFlowUnits.capacity_spec B (variableIndex n v).val
      (((variableIndex n v).val-1)%(n*n)) (rowIndex n (.inl (a,b))).val h1 hv hcarB hr ν
        ⟨hctxν.2.2.2.2.1,harc,hctxν.2.2.2.1⟩
    refine ⟨τ,(hprep.seq (Run.ite_true hcond hcap)).mono (by simp [Cond.size,Expr.size]), ?_⟩
    cases v with
    | inl v => simpa only [RamFlowUnits.capacityValue,value_variable,if_true,DirectedFlowLP.coefficient] using hpost
    | inr ca =>
      rcases ca with ⟨⟨s,t⟩,⟨u,v⟩⟩
      have hcol : (variableIndex n (.inr ((s,t),(u,v)))).val ≠ 0 := by rw [arc_variable]; omega
      simpa only [RamFlowUnits.capacityValue,if_neg hcol,arc_mod,capacity_row,←edge_value,
        edge_equal,DirectedFlowLP.coefficient] using hpost
  | inr b =>
    rcases b with ⟨flag,⟨⟨s,t⟩,u⟩⟩
    have hi : ¬(rowIndex n (.inr (flag,((s,t),u)))).val < n*n := by rw [balance_row]; omega
    have hcond : (Cond.lt (.var "lp.i") (.var "lp.n2")).evalB B ν = some false := by
      rw [evalB_condLt_iff]
      exact ⟨(rowIndex n (.inr (flag,((s,t),u)))).val,n*n,
        by rw [evalB_var_iff]; exact ⟨hctxν.2.2.2.1.symm,hctxν.2.2.2.1 ▸ hr⟩,
        by rw [evalB_var_iff]; exact ⟨hctxν.2.1.symm,hctxν.2.1 ▸ hn2⟩,by simp [hi]⟩
    have hs' : ν.vars "lp.s" = s.val := by rwa [row_mod,balance_div,edge_div] at hs
    have ht' : ν.vars "lp.t" = t.val := by rwa [row_mod,balance_div,edge_mod] at ht
    have hu' : ν.vars "lp.u" = u.val := by rwa [row_mod,balance_mod] at hu
    have hc' : ν.vars "lp.commodity" = (edgeIndex n (s,t)).val := by rwa [row_mod,balance_div] at hcom
    have hf' : ν.vars "lp.sign" = flag.val := by rwa [row_div] at hflag
    obtain ⟨μ,hbase,hbasePost⟩ := RamFlowBalance.command_spec B M I s t u v hB hni hn2 hv hnum hden ν
      ⟨hctxν.2.2.2.2.2,hs',ht',hu',hc',hctxν.2.2.2.2.1,hac,has,hat⟩
    have hfμ : μ.vars "lp.sign" = flag.val := (hbase.frame_var "lp.sign" (by decide)).trans hf'
    have hflagB : flag.val < B := flag.isLt.trans_le (by omega : 2 ≤ B)
    obtain ⟨τ,hsign,hpost⟩ := RamFlowUnits.rowSign_spec B flag.val
      (DirectedFlowLP.balanceCoefficient I ((s,t),u) v) h1 hflagB μ ⟨hbasePost,hfμ⟩
    refine ⟨τ,(hprep.seq (Run.ite_false hcond (hbase.seq hsign))).mono
      (by simp only [Cond.size,Expr.size]; omega), ?_⟩
    have hz : flag.val = 0 ↔ flag = 0 := by rw [←Fin.val_inj]; rfl
    simpa only [DirectedFlowLP.coefficient,hz] using hpost

end Lax455465Proofs.RamFlowCoefficient
