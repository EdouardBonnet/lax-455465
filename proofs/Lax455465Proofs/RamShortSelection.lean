import Lax455465Proofs.ShortLayerScan

namespace Lax455465Proofs.RamShortSelection
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

/-- A bounded first-success search, followed by conversion from the scan's
zero-based index to the positive path-length budget. -/
def command (trial : Com) : Com :=
  .seq (.assign "find.count" (.sub (.var "lp.n") (.lit 1)))
  (.seq (RamFind.command trial)
    (.assign "short.layer" (.add (.var "find.result") (.lit 1))))

def names : List String := ["find.count","find.i","find.found","find.result","short.layer"]

/-- The fixed trial command must compute the stopping predicate from its
current LP. No stopping decision is provided as initialized input data. -/
theorem command_spec (B K n : ℕ) (hn : 2 ≤ n) (hnB : n < B)
    (capacity : ℚ) (value : ℕ → ℚ) (R : Env → Prop) (trial : Com)
    (horder : ∀ σ,R σ→σ.vars "lp.n"=n)
    (hset : ∀ σ k name,R σ→name∈names→R (σ.setVar name k))
    (htrial : ∀ i,i<n-1→Spec B (fun σ => R σ ∧ σ.vars "find.i"=i) trial
      (fun _ τ => R τ ∧ τ.vars "find.ok"=if ShortLayerScan.predicate n capacity value i then 1 else 0) K)
    (hframe : ∀ x∈["find.i","find.found","find.result","find.count"],x∉trial.wvars) :
    Spec B R (command trial)
      (fun _ τ => R τ ∧ τ.vars "short.layer"=ShortLayerSelection.select n capacity value)
      ((K+20)*(n-1)+18) := by
  let Q := fun σ : Env => R σ ∧ σ.vars "find.count"=n-1
  have h1 : 1<B := by omega
  have hscan := RamFind.command_spec B (n-1) K Q (ShortLayerScan.predicate n capacity value) trial
    h1 (by omega) (fun _ h => h.2)
    (by
      intro σ k name h hm
      refine ⟨hset σ k name h.1 ?_,?_⟩
      · simp only [names,List.mem_cons,List.not_mem_nil,or_false] at hm ⊢
        tauto
      · simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
        rcases hm with rfl | rfl | rfl
        all_goals first
          | simpa only [vars_setVar,String.reduceEq,if_false] using h.2
)
    (by
      intro i hi σ hσ
      obtain ⟨τ,rr,pr⟩ := htrial i hi σ ⟨hσ.1.1,hσ.2⟩
      exact ⟨τ,rr,⟨pr.1,(rr.frame_var "find.count" (hframe _ (by simp))).trans hσ.1.2⟩,pr.2⟩)
    ⟨hframe _ (by simp),hframe _ (by simp),hframe _ (by simp)⟩
  intro σ hR
  let ν := σ.setVar "find.count" (n-1)
  have hnσ := horder σ hR
  have ri : Run B (.assign "find.count" (.sub (.var "lp.n") (.lit 1))) σ ν 4 :=
    Run.assign (evalB_bin (op := .sub)
      (by rw [evalB_var_iff]; exact ⟨hnσ.symm,hnσ ▸ hnB⟩) (evalB_lit h1) (by dsimp [Bop.apply]; omega))
  have hν : Q ν := ⟨hset σ (n-1) "find.count" hR (by simp [names]),by simp [ν]⟩
  obtain ⟨μ,rs,ps⟩ := hscan ν hν
  have hm : μ.vars "find.found"=1 ∧ μ.vars "find.result"=ShortLayerSelection.select n capacity value-1 := by
    simpa only [ShortLayerScan.selected n hn capacity value,RamFind.Matches] using ps.2
  obtain ⟨hlo,hhi⟩ := ShortLayerSelection.select_range n hn capacity value
  let τ := μ.setVar "short.layer" (ShortLayerSelection.select n capacity value)
  have re : Run B (.assign "short.layer" (.add (.var "find.result") (.lit 1))) μ τ 4 := by
    have hh := Run.assign (σ := μ) (x := "short.layer")
      (evalB_bin (op := .add)
        (by rw [evalB_var_iff]; exact ⟨hm.2.symm,hm.2 ▸ (by omega : ShortLayerSelection.select n capacity value-1 < B)⟩)
        (evalB_lit h1) (by dsimp [Bop.apply]; omega))
    simpa only [Bop.apply,Nat.sub_add_cancel hlo,Expr.size] using hh
  exact ⟨τ,(ri.seq (rs.seq re)).mono (by omega),
    hset μ _ "short.layer" ps.1.1 (by simp [names]),by simp [τ]⟩

end Lax455465Proofs.RamShortSelection
