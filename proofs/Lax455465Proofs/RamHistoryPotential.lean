import Lax455465Proofs.RamHistoryLabel

set_option maxRecDepth 8192
namespace Lax455465Proofs.RamHistoryPotential
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar RamRegionRecord RamRegionContext
open Lax455465.RationalEncoding HistoryPotentialData
open scoped NNRat

def Context {n : ℕ} (d : MetricMatrix.Matrix n) (history : List (Entry n)) (σ : Env) : Prop :=
  σ.vars "metric.n"=n ∧ σ.vars "find.count"=history.length ∧
    Prefix (RamUnsignedBuffer.encode (MetricMatrix.values d)) "metric.old" σ ∧ Prefix (words history) "region.history" σ

theorem frame {B K : ℕ} {cmd : Com} {σ τ : Env} (rr : Run B cmd σ τ K)
    {n : ℕ} {d : MetricMatrix.Matrix n} {history : List (Entry n)} (h : Context d history σ)
    (hx : ∀ x∈["metric.n","find.count"],x∉cmd.wvars)
    (ha : ∀ a∈["metric.old","region.history"],a∉cmd.warrs) : Context d history τ := by
  simpa only [Context,Prefix,rr.frame_var "metric.n" (hx _ (by simp)),rr.frame_var "find.count" (hx _ (by simp)),
    rr.frame_arr "metric.old" (ha _ (by simp)),rr.frame_arr "region.history" (ha _ (by simp))] using h

def vector : Com := .seq (.assign "history.potentialPos" (.lit 0))
  (RamUnsignedVector.command "history.vertex" "metric.n" "cut.potential" "history.potentialPos" RamHistoryLabel.command)
def command : Com := .seq (.assign "find.count" (.div (.var "history.pos") (.lit 4)))
  (.seq vector (.seq (.assign "cut.reversed" (.lit 1)) (.assign "cut.count" (.var "metric.n"))))
def cost (n m : ℕ) : ℕ := (140*m+74)*n+16

theorem vector_spec (B M : ℕ) {n : ℕ} (d : MetricMatrix.Matrix n) (history : List (Entry n))
    (hM : 1 ≤ M) (hm : 2*history.length ≤ M) (hB : 2*M^2+3 < B) (h4 : 4 < B)
    (hlen : 4*history.length < B) (hindex : 2*(n*n)+2 < B) (hvertex : 2*n+2 < B)
    (hd : ∀ u w,LpInputSize.Height M (d u w : ℚ)) (hr : ∀ e∈history,LpInputSize.Height M (e.radius : ℚ)) :
    Spec B (fun σ => Context d history σ ∧ 2*n < (σ.arrs "cut.potential").length) vector
      (fun _ τ => Context d history τ ∧ Prefix (RamUnsignedBuffer.encode (List.ofFn (values d history))) "cut.potential" τ)
      ((140*history.length+74)*n+8) := by
  let qs := List.ofFn (values d history)
  have hMB : M < B := by nlinarith
  have hheight (i : ℕ) (hi : i < qs.length) : LpInputSize.Height M (qs[i] : ℚ) := by
    simp only [qs,List.getElem_ofFn]
    exact value_height d history M hM hm _
  have hloop := RamUnsignedVector.command_spec B (RamHistoryLabel.cost history.length) (Context d history)
    "history.vertex" "metric.n" "cut.potential" "history.potentialPos" qs [] RamHistoryLabel.command (by omega)
    (by simpa only [qs,List.length_nil,List.length_ofFn,Nat.zero_add] using hvertex)
    (fun i hi => (num_bound (hheight i hi)).trans_lt hMB)
    (fun i hi => (den_bound (hheight i hi)).trans_lt hMB)
    (fun σ h => by simpa only [qs,List.length_ofFn] using h.1)
    (fun σ k h => by simpa only [Context,Prefix,vars_setVar,arrs_setVar,String.reduceEq,if_false] using h)
    (fun i hi σ hσ => by
      have hi' : i < n := by simpa only [qs,List.length_ofFn] using hi
      obtain ⟨τ,rr,pr⟩ := RamHistoryLabel.command_spec B M d history ⟨i,hi'⟩ hB h4 hlen hindex (by omega) hd hr σ
        ⟨hσ.1.1,hσ.1.2.1,hσ.2,hσ.1.2.2⟩
      exact ⟨τ,rr,⟨pr.1.1,pr.1.2.1,pr.1.2.2.2⟩,by simpa only [qs,List.getElem_ofFn] using pr.2⟩)
    (by decide) (by decide) (by decide) (by decide)
    (fun rr h => frame rr h (by decide) (by decide)) (by decide) (by decide)
  rintro σ ⟨hσ,hroom⟩
  let ν := σ.setVar "history.potentialPos" 0
  have rz : Run B (.assign "history.potentialPos" (.lit 0)) σ ν 2 := Run.assign (evalB_lit (by omega))
  have hν := frame rz hσ (by decide) (by decide)
  obtain ⟨τ,rl,pl⟩ := hloop ν ⟨hν,by intro i hi; simp at hi,by simp [ν],
    by simpa only [ν,arrs_setVar,qs,List.length_nil,List.length_ofFn,Nat.zero_add] using hroom⟩
  exact ⟨τ,(rz.seq rl).mono (by simp only [qs,List.length_ofFn,RamHistoryLabel.cost,Nat.add_assoc,Nat.reduceAdd]; omega),
    pl.1,by simpa only [List.nil_append,qs] using pl.2.1⟩

/-- Read the complete runtime history and emit each vertex's integer
position as a canonical nonnegative rational, ready for an upper sweep. -/
theorem command_spec (B M : ℕ) {n : ℕ} (d : MetricMatrix.Matrix n) (history : List (Entry n))
    (hM : 1 ≤ M) (hm : 2*history.length ≤ M) (hB : 2*M^2+3 < B) (h4 : 4 < B)
    (hlen : 4*history.length < B) (hindex : 2*(n*n)+2 < B) (hvertex : 2*n+2 < B)
    (hd : ∀ u w,LpInputSize.Height M (d u w : ℚ)) (hr : ∀ e∈history,LpInputSize.Height M (e.radius : ℚ)) :
    Spec B (fun σ => σ.vars "metric.n"=n ∧ σ.vars "history.pos"=4*history.length ∧
      Prefix (RamUnsignedBuffer.encode (MetricMatrix.values d)) "metric.old" σ ∧ Prefix (words history) "region.history" σ ∧
      2*n < (σ.arrs "cut.potential").length) command
      (fun _ τ => Context d history τ ∧ τ.vars "cut.reversed"=1 ∧ τ.vars "cut.count"=n ∧
        Prefix (RamUnsignedBuffer.encode (List.ofFn (values d history))) "cut.potential" τ) (cost n history.length) := by
  rintro σ ⟨hn,hpos,hdσ,hhσ,hroom⟩
  let ν := σ.setVar "find.count" history.length
  have r1 : Run B (.assign "find.count" (.div (.var "history.pos") (.lit 4))) σ ν 4 := by
    have he : (Expr.div (.var "history.pos") (.lit 4)).evalB B σ=some history.length := by
      simpa [Bop.apply] using evalB_bin (op := .div)
        (show (Expr.var "history.pos").evalB B σ=some (4*history.length) from by
          rw [evalB_var_iff]; exact ⟨hpos.symm,hpos ▸ hlen⟩) (evalB_lit h4) (by dsimp [Bop.apply]; omega)
    exact Run.assign he
  have hν : Context d history ν := ⟨by simpa [ν] using hn,by simp [ν],hdσ,hhσ⟩
  obtain ⟨μ,r2,p2⟩ := vector_spec B M d history hM hm hB h4 hlen hindex hvertex hd hr ν ⟨hν,hroom⟩
  let ξ := μ.setVar "cut.reversed" 1
  let τ := ξ.setVar "cut.count" n
  have r3 : Run B (.assign "cut.reversed" (.lit 1)) μ ξ 2 := Run.assign (evalB_lit (by omega))
  have r4 : Run B (.assign "cut.count" (.var "metric.n")) ξ τ 2 := Run.assign (by
    rw [evalB_var_iff]
    exact ⟨by simpa only [ξ,vars_setVar,String.reduceEq,if_false] using p2.1.1.symm,
      by simp only [ξ,vars_setVar,String.reduceEq,if_false,p2.1.1]; omega⟩)
  refine ⟨τ,(r1.seq (r2.seq (r3.seq r4))).mono (by dsimp [cost]; omega),
    frame (r3.seq r4) p2.1 (by decide) (by decide),by simp [τ,ξ],by simp [τ],p2.2⟩

end Lax455465Proofs.RamHistoryPotential
