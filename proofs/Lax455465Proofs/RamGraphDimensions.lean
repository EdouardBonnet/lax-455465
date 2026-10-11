import Lax455465Proofs.RamFlowDimensions
import Lax455465Proofs.RamFlowData

namespace Lax455465Proofs.RamGraphDimensions

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamFlowData

def Dimensions (n : ℕ) (σ : Env) : Prop :=
  σ.vars "lp.n" = n ∧ σ.vars "lp.n2" = n*n ∧ σ.vars "lp.n3" = (n*n)*n ∧
    σ.vars "lp.rows" = rows n ∧ σ.vars "lp.columns" = columns n ∧
    σ.vars "lp.matrixLength" = rows n*columns n

def command : Com := .seq RamFlowDimensions.command
  (.assign "lp.matrixLength" (.mul (.var "lp.rows") (.var "lp.columns")))

theorem command_spec (B n : ℕ) (h2 : 2 < B) (hn : n < B) (hn2 : n*n < B) (hn3 : (n*n)*n < B)
    (hr : rows n < B) (hc : columns n < B) (hm : rows n*columns n < B) :
    Spec B (fun σ => σ.vars "lp.n" = n) command (fun _ τ => Dimensions n τ) 24 := by
  rintro σ hN
  obtain ⟨ν,hdims,hpost⟩ := RamFlowDimensions.command_spec B n h2 hn hn2 hn3 hr hc σ hN
  have he : (Expr.mul (.var "lp.rows") (.var "lp.columns")).evalB B ν = some (rows n*columns n) :=
    evalB_bin (op := .mul) (by rw [evalB_var_iff]; exact ⟨hpost.2.2.2.1.symm,hpost.2.2.2.1 ▸ hr⟩)
      (by rw [evalB_var_iff]; exact ⟨hpost.2.2.2.2.symm,hpost.2.2.2.2 ▸ hc⟩) hm
  refine ⟨ν.setVar "lp.matrixLength" (rows n*columns n),hdims.seq (Run.assign he),?_,?_,?_,?_,?_,?_⟩
  all_goals simp only [vars_setVar,String.reduceEq,if_false,if_true]
  all_goals first | assumption | rfl | exact hpost.1 | exact hpost.2.1 | exact hpost.2.2.1 | exact hpost.2.2.2.1 | exact hpost.2.2.2.2

/-- Input decoding phases retain all computed dimensions. -/
theorem frame {B K : ℕ} {c : Com} {σ τ : Env} (hr : Run B c σ τ K) (n : ℕ) (h : Dimensions n σ)
    (hx : ∀ x ∈ ["lp.n","lp.n2","lp.n3","lp.rows","lp.columns","lp.matrixLength"], x ∉ c.wvars) :
    Dimensions n τ := by
  have hn := hr.frame_var "lp.n" (hx _ (by simp))
  have hn2 := hr.frame_var "lp.n2" (hx _ (by simp))
  have hn3 := hr.frame_var "lp.n3" (hx _ (by simp))
  have hrows := hr.frame_var "lp.rows" (hx _ (by simp))
  have hcols := hr.frame_var "lp.columns" (hx _ (by simp))
  have htotal := hr.frame_var "lp.matrixLength" (hx _ (by simp))
  simpa only [Dimensions,hn,hn2,hn3,hrows,hcols,htotal] using h

end Lax455465Proofs.RamGraphDimensions
