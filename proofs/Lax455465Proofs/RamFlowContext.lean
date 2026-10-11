import Lax455465Proofs.RamWeightProduct
import Lax455465Proofs.DirectedFlowLP

namespace Lax455465Proofs.RamFlowContext

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState DirectedFlowLP
open scoped NNRat

/-- Runtime data that coefficient evaluation must preserve. -/
def Context (n i j : ℕ) (weights : List ℚ≥0) (σ : Env) : Prop :=
  σ.vars "lp.n" = n ∧ σ.vars "lp.n2" = n*n ∧ σ.vars "lp.n3" = (n*n)*n ∧
    σ.vars "lp.i" = i ∧ σ.vars "lp.j" = j ∧
      Prefix (RamUnsignedBuffer.encode weights) "flow.weights" σ

theorem frame {B K : ℕ} {c : Com} {σ τ : Env} (hr : Run B c σ τ K)
    (n i j : ℕ) (weights : List ℚ≥0) (h : Context n i j weights σ)
    (ha : "flow.weights" ∉ c.warrs)
    (hx : ∀ x ∈ ["lp.n","lp.n2","lp.n3","lp.i","lp.j"], x ∉ c.wvars) :
    Context n i j weights τ := by
  have hn := hr.frame_var "lp.n" (hx _ (by simp))
  have hn2 := hr.frame_var "lp.n2" (hx _ (by simp))
  have hn3 := hr.frame_var "lp.n3" (hx _ (by simp))
  have hi := hr.frame_var "lp.i" (hx _ (by simp))
  have hj := hr.frame_var "lp.j" (hx _ (by simp))
  have harr := hr.frame_arr "flow.weights" ha
  simpa only [Context,Prefix,hn,hn2,hn3,hi,hj,harr] using h

end Lax455465Proofs.RamFlowContext
