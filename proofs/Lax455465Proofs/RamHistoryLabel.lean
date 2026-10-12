import Lax455465Proofs.HistoryPotentialData
import Lax455465Proofs.RamHistoryTest

set_option maxRecDepth 8192
namespace Lax455465Proofs.RamHistoryLabel
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar RamRegionRecord RamRegionContext
open Lax455465.RationalEncoding HistoryPotentialData RamHistoryTest
open scoped NNRat

def position : Com := .ite (.eq (.var "history.outward") (.lit 1))
  (.assign "rat.n" (.sub (.mul (.lit 2) (.var "find.count")) (.var "find.result")))
  (.assign "rat.n" (.var "find.result"))
def choose : Com := .ite (.eq (.var "find.found") (.lit 1))
  (.seq (.assign "find.i" (.var "find.result")) (.seq RamHistoryEntry.command position))
  (.assign "rat.n" (.var "find.count"))
def finish : Com := .seq (.assign "rat.d" (.lit 1)) (.assign "rat.s" (.lit 0))
def command : Com := .seq (RamFind.command RamHistoryTest.command) (.seq choose finish)
def cost (m : ℕ) : ℕ := 140*m+52

theorem position_spec (B m j : ℕ) (outward : Bool) (h2 : 2 < B) (hj : j < m) (hm : 2*m < B) :
    Spec B (fun σ => σ.vars "find.count"=m ∧ σ.vars "find.result"=j ∧
      σ.vars "history.outward"=(if outward then 1 else 0)) position
      (fun _ τ => τ.vars "rat.n"=(if outward then 2*m-j else j)) 10 := by
  rintro σ ⟨hmσ,hjσ,hoσ⟩
  have hmB : m < B := by omega
  have hjB : j < B := by omega
  have hout : 2*m-j < B := by omega
  cases outward <;> run_vcg <;> simp_all <;> omega

theorem finish_spec (B a : ℕ) (h1 : 1 < B) :
    Spec B (fun σ => σ.vars "rat.n"=a) finish (fun _ τ => RamRational.FractionOutput (a : ℚ) τ) 4 := by
  intro σ hσ
  run_vcg
  all_goals simp_all [RamRational.FractionOutput,RamRational.fractionValue]

theorem choose_spec (B M : ℕ) {n : ℕ} (d : MetricMatrix.Matrix n) (history : List (Entry n)) (v : Fin n)
    (hMB : M < B) (h4 : 4 < B) (hlen : 4*history.length < B) (hn : n < B)
    (hr : ∀ e∈history,LpInputSize.Height M (e.radius : ℚ)) :
    Spec B (fun σ => Context d history v σ ∧ RamFind.Matches (RamFind.first (predicate d history v) history.length) σ)
      choose (fun _ τ => Context d history v τ ∧ τ.vars "rat.n"=(values d history v).num) 38 := by
  rintro σ ⟨hσ,hmatch⟩
  cases he : RamFind.first (predicate d history v) history.length with
  | none =>
    have hf : σ.vars "find.found"=0 := by simpa only [he,RamFind.Matches] using hmatch
    have hc : (Cond.eq (.var "find.found") (.lit 1)).evalB B σ=some false := by
      rw [evalB_condEq (evalB_var (hf ▸ (by omega : 0 < B))) (evalB_lit (by omega)),hf]
      rfl
    have ra : Run B (.assign "rat.n" (.var "find.count")) σ (σ.setVar "rat.n" history.length) 2 :=
      Run.assign (by rw [evalB_var_iff]; exact ⟨hσ.2.1.symm,hσ.2.1 ▸ (by omega : history.length < B)⟩)
    have rr := Run.ite_false (c := .seq (.assign "find.i" (.var "find.result")) (.seq RamHistoryEntry.command position)) hc ra
    refine ⟨_,rr.mono (by decide),frame rr hσ (by decide) (by decide),?_⟩
    simp [value_none d history v he]
  | some j =>
    have hj := (RamFind.first_some _ _ _ he).1
    have hm : σ.vars "find.found"=1 ∧ σ.vars "find.result"=j := by simpa only [he,RamFind.Matches] using hmatch
    have hjB : j < B := by omega
    have hc : (Cond.eq (.var "find.found") (.lit 1)).evalB B σ=some true := by
      rw [evalB_condEq (evalB_var (hm.1 ▸ (by omega : 1 < B))) (evalB_lit (by omega)),hm.1]
      rfl
    let σ1 := σ.setVar "find.i" j
    have r1 : Run B (.assign "find.i" (.var "find.result")) σ σ1 2 :=
      Run.assign (by rw [evalB_var_iff]; exact ⟨hm.2.symm,hm.2 ▸ hjB⟩)
    have h1 := frame r1 hσ (by decide) (by decide)
    have hrj := hr history[j] (List.getElem_mem hj)
    obtain ⟨σ2,r2,p2⟩ := RamHistoryEntry.command_spec B history j hj h4 hlen hn
      ((num_bound hrj).trans_lt hMB) ((den_bound hrj).trans_lt hMB) σ1 ⟨h1.2.2.2.2,by simp [σ1]⟩
    have h2 := frame r2 h1 (by decide) (by decide)
    have hj2 : σ2.vars "find.result"=j := ((r1.seq r2).frame_var _ (by decide)).trans hm.2
    obtain ⟨τ,r3,p3⟩ := position_spec B history.length j history[j].outward (by omega) hj (by omega) σ2 ⟨h2.2.1,hj2,p2.2.2⟩
    have rr := Run.ite_true (d := .assign "rat.n" (.var "find.count")) hc (r1.seq (r2.seq r3))
    refine ⟨τ,rr,frame rr hσ (by decide) (by decide),?_⟩
    rw [value_some d history v j he hj]
    change τ.vars "rat.n"=(if history[j].outward then 2*history.length-j else j)
    exact p3

/-- Return the exact ordering position of the first region containing a
vertex, using the middle position when no recorded ball contains it. -/
theorem command_spec (B M : ℕ) {n : ℕ} (d : MetricMatrix.Matrix n) (history : List (Entry n)) (v : Fin n)
    (hB : 2*M^2+3 < B) (h4 : 4 < B) (hlen : 4*history.length < B) (hindex : 2*(n*n)+2 < B) (hn : n < B)
    (hd : ∀ u w,LpInputSize.Height M (d u w : ℚ)) (hr : ∀ e∈history,LpInputSize.Height M (e.radius : ℚ)) :
    Spec B (Context d history v) command
      (fun _ τ => Context d history v τ ∧ RamRational.FractionOutput (values d history v : ℚ) τ)
      (cost history.length) := by
  have hMB : M < B := by nlinarith
  have hscan := RamFind.command_spec B history.length 120 (Context d history v) (predicate d history v)
    RamHistoryTest.command (by omega) (by omega) (fun _ h => h.2.1)
    (fun σ k name h hname => by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hname
      rcases hname with rfl | rfl | rfl <;> simpa only [Context,Prefix,vars_setVar,arrs_setVar,String.reduceEq,if_false] using h)
    (fun i hi σ hσ => by
      obtain ⟨τ,rr,pr⟩ := RamHistoryTest.command_spec B M d history v i hi hB h4 hlen hindex hn hd hr σ hσ
      refine ⟨τ,rr,pr.1,?_⟩
      cases he : history[i].outward <;>
        simpa only [predicate_at d history v i hi,contains,pair,he,Bool.false_eq_true,if_false,if_true,
          decide_eq_true_eq] using pr.2) (by decide)
  intro σ hσ
  obtain ⟨σ1,r1,p1⟩ := hscan σ hσ
  obtain ⟨σ2,r2,p2⟩ := choose_spec B M d history v hMB h4 hlen hn hr σ1 p1
  obtain ⟨τ,r3,p3⟩ := finish_spec B (values d history v).num (by omega) σ2 p2.2
  have rr := r1.seq (r2.seq r3)
  refine ⟨τ,rr.mono (by simp [cost]),frame rr hσ (by decide) (by decide),?_⟩
  simpa [values] using p3

end Lax455465Proofs.RamHistoryLabel
