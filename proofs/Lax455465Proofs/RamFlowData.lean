import Lax455465Proofs.RamFlowContext

namespace Lax455465Proofs.RamFlowData

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState DirectedFlowLP
open scoped NNRat

abbrev rows (n : ℕ) := n*n+2*((n*n)*n)
abbrev columns (n : ℕ) := 1+(n*n)*(n*n)

def capacities {n : ℕ} (I : Lax455465.RationalEncoding.RationalInstance n) : List ℚ≥0 :=
  List.ofFn fun e : Fin (n*n) => I.capacity ((edgeIndex n).symm e).1 ((edgeIndex n).symm e).2

/-- Initialized graph data and dimensions shared by all construction loops. -/
def Data {n : ℕ} (I : Lax455465.RationalEncoding.RationalInstance n) (σ : Env) : Prop :=
  σ.vars "lp.n" = n ∧ σ.vars "lp.n2" = n*n ∧ σ.vars "lp.n3" = (n*n)*n ∧
    σ.vars "lp.rows" = rows n ∧ σ.vars "lp.columns" = columns n ∧
    σ.vars "lp.matrixLength" = rows n*columns n ∧
    Prefix (RamUnsignedBuffer.encode (List.ofFn I.weight)) "flow.weights" σ ∧
    Prefix (RamUnsignedBuffer.encode (capacities I)) "flow.capacities" σ

theorem frame {B K : ℕ} {c : Com} {σ τ : Env} (hr : Run B c σ τ K)
    {n : ℕ} (I : Lax455465.RationalEncoding.RationalInstance n) (h : Data I σ)
    (ha : ∀ a ∈ ["flow.weights","flow.capacities"], a ∉ c.warrs)
    (hx : ∀ x ∈ ["lp.n","lp.n2","lp.n3","lp.rows","lp.columns","lp.matrixLength"], x ∉ c.wvars) :
    Data I τ := by
  have hn := hr.frame_var "lp.n" (hx _ (by simp))
  have hn2 := hr.frame_var "lp.n2" (hx _ (by simp))
  have hn3 := hr.frame_var "lp.n3" (hx _ (by simp))
  have hrows := hr.frame_var "lp.rows" (hx _ (by simp))
  have hcols := hr.frame_var "lp.columns" (hx _ (by simp))
  have htotal := hr.frame_var "lp.matrixLength" (hx _ (by simp))
  have hw := hr.frame_arr "flow.weights" (ha _ (by simp))
  have hc := hr.frame_arr "flow.capacities" (ha _ (by simp))
  simpa only [Data,Prefix,hn,hn2,hn3,hrows,hcols,htotal,hw,hc] using h

/-- Loop indices can be reset or advanced without changing source data. -/
theorem set_index {n : ℕ} (I : Lax455465.RationalEncoding.RationalInstance n) (σ : Env)
    (index : String) (k : ℕ) (h : Data I σ)
    (hx : ∀ x ∈ ["lp.n","lp.n2","lp.n3","lp.rows","lp.columns","lp.matrixLength"], x ≠ index) :
    Data I (σ.setVar index k) := by
  simpa only [Data,Prefix,vars_setVar,arrs_setVar,if_neg (hx "lp.n" (by simp)),if_neg (hx "lp.n2" (by simp)),
    if_neg (hx "lp.n3" (by simp)),if_neg (hx "lp.rows" (by simp)),
    if_neg (hx "lp.columns" (by simp)),if_neg (hx "lp.matrixLength" (by simp))] using h

end Lax455465Proofs.RamFlowData
