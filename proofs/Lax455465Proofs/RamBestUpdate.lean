import Lax455465Proofs.BestCutIndex
import Lax455465Proofs.RamScalarComparison
import Lax455465Proofs.RamRoundingConstants

namespace Lax455465Proofs.RamBestUpdate
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar RamRegionContext
open scoped NNRat

def Matches (value : ℕ → ℚ≥0) : Option ℕ → Env → Prop
  | none, σ => σ.vars "best.found"=0
  | some j, σ => σ.vars "best.found"=1 ∧ σ.vars "best.index"=j ∧ Stored "best.value" (value j) σ

def Current (valid : ℕ → Prop) [DecidablePred valid] (value : ℕ → ℚ≥0) (i : ℕ) (σ : Env) : Prop :=
  σ.vars "cut.candidate"=i ∧ σ.vars "cut.valid"=(if valid i then 1 else 0) ∧ Stored "cut.ratio" (value i) σ

def update : Com := .seq (.assign "best.index" (.var "cut.candidate"))
  (.seq (.assign "best.value.n" (.var "cut.ratio.n"))
    (.seq (.assign "best.value.d" (.var "cut.ratio.d")) (.assign "best.found" (.lit 1))))
def compare : Com := .seq (RamScalarComparison.command "best.value" "cut.ratio")
  (.ite (.eq (.var "cmp.le") (.lit 0)) update .skip)
def choose : Com := .ite (.eq (.var "best.found") (.lit 0)) update compare

def command : Com := .ite (.eq (.var "cut.valid") (.lit 1)) choose .skip

theorem update_spec (B : ℕ) (i : ℕ) (q : ℚ≥0) (hi : i<B) (hn : q.num<B) (hd : q.den<B) (h1 : 1<B) :
    Spec B (fun σ => σ.vars "cut.candidate"=i ∧ Stored "cut.ratio" q σ) update
      (fun _ τ => τ.vars "best.found"=1 ∧ τ.vars "best.index"=i ∧ Stored "best.value" q τ) 8 := by
  rintro σ ⟨hidx,hq⟩
  run_vcg
  all_goals simp_all [Stored]

set_option maxHeartbeats 2400000 in
/-- A single native update retains a strict improvement among positive-demand
cuts. Invalid shores are skipped; equal ratios preserve the earlier index. -/
theorem command_spec (B M : ℕ) (valid : ℕ → Prop) [DecidablePred valid] (value : ℕ → ℚ≥0)
    (i : ℕ) (old : Option ℕ) (hB : 2*M^2+3<B) (hi : i<B)
    (hcur : LpInputSize.Height M (value i : ℚ))
    (hold : ∀ j, old=some j → LpInputSize.Height M (value j : ℚ)) :
    Spec B (fun σ => Current valid value i σ ∧ Matches value old σ) command
      (fun _ τ => Current valid value i τ ∧ Matches value (BestCutIndex.next valid value i old) τ) 84 := by
  have hMB : M<B := by nlinarith
  have h1 : 1<B := by nlinarith
  have currentFrame {cmd : Com} {σ τ : Env} {K : ℕ} (rr : Run B cmd σ τ K) (h : Current valid value i σ)
      (hx : ∀ x∈["cut.candidate","cut.valid","cut.ratio.n","cut.ratio.d"], x∉cmd.wvars) : Current valid value i τ := by
    exact ⟨(rr.frame_var _ (hx _ (by simp))).trans h.1,(rr.frame_var _ (hx _ (by simp))).trans h.2.1,
      RamRoundingConstants.storedFrame rr h.2.2 (hx _ (by simp)) (hx _ (by simp))⟩
  rintro σ ⟨hσ,holdσ⟩
  by_cases hv : valid i
  · have hvalid : σ.vars "cut.valid"=1 := by simpa only [if_pos hv] using hσ.2.1
    have hc : (Cond.eq (.var "cut.valid") (.lit 1)).evalB B σ=some true := by
      rw [evalB_condEq (evalB_var (hvalid ▸ h1)) (evalB_lit h1),hvalid]
      rfl
    cases old with
    | none =>
      have hf : σ.vars "best.found"=0 := holdσ
      have hfound : (Cond.eq (.var "best.found") (.lit 0)).evalB B σ=some true := by
        rw [evalB_condEq (evalB_var (hf ▸ (by omega : 0<B))) (evalB_lit (by omega)),hf]
        rfl
      obtain ⟨τ,ru,pu⟩ := update_spec B i (value i) hi ((num_bound hcur).trans_lt hMB) ((den_bound hcur).trans_lt hMB) h1 σ ⟨hσ.1,hσ.2.2⟩
      have rr := Run.ite_true (d := .skip) hc (Run.ite_true (d := compare) hfound ru)
      exact ⟨τ,rr.mono (by dsimp [Cond.size,Expr.size]; omega),currentFrame rr hσ (by decide),
        by simpa only [BestCutIndex.next,if_pos hv,Matches] using pu⟩
    | some j =>
      have hj : LpInputSize.Height M (value j : ℚ) := hold j rfl
      have hf : σ.vars "best.found"=1 := holdσ.1
      have hfound : (Cond.eq (.var "best.found") (.lit 0)).evalB B σ=some false := by
        rw [evalB_condEq (evalB_var (hf ▸ h1)) (evalB_lit (by omega)),hf]
        rfl
      obtain ⟨ν,rc,pc⟩ := RamScalarComparison.command_spec B M (value j) (value i) "best.value" "cut.ratio" hB
        (num_bound hj) (den_bound hj) (num_bound hcur) (den_bound hcur) (by decide) (by decide) (by decide) σ ⟨holdσ.2.2,hσ.2.2⟩
      have hν := currentFrame rc hσ (by decide)
      by_cases hbetter : value i<value j
      · have hcmp : ν.vars "cmp.le"=0 := by
          simpa only [NNRat.coe_le_coe,if_neg (not_le.mpr hbetter)] using pc
        have htest : (Cond.eq (.var "cmp.le") (.lit 0)).evalB B ν=some true := by
          rw [evalB_condEq (evalB_var (hcmp ▸ (by omega : 0<B))) (evalB_lit (by omega)),hcmp]
          rfl
        obtain ⟨τ,ru,pu⟩ := update_spec B i (value i) hi ((num_bound hcur).trans_lt hMB) ((den_bound hcur).trans_lt hMB) h1 ν ⟨hν.1,hν.2.2⟩
        have rr := Run.ite_true (d := .skip) hc (Run.ite_false (c := update) hfound
          (rc.seq (Run.ite_true (d := .skip) htest ru)))
        exact ⟨τ,rr.mono (by dsimp [Cond.size,Expr.size]; omega),currentFrame rr hσ (by decide),
          by simpa only [BestCutIndex.next,if_pos (And.intro hv hbetter),Matches] using pu⟩
      · have hcmp : ν.vars "cmp.le"=1 := by
          simpa only [NNRat.coe_le_coe,if_pos (le_of_not_gt hbetter)] using pc
        have htest : (Cond.eq (.var "cmp.le") (.lit 0)).evalB B ν=some false := by
          rw [evalB_condEq (evalB_var (hcmp ▸ h1)) (evalB_lit (by omega)),hcmp]
          rfl
        have rr := Run.ite_true (d := .skip) hc (Run.ite_false (c := update) hfound
          (rc.seq (Run.ite_false (c := update) htest Run.skip)))
        refine ⟨ν,rr.mono (by dsimp [Cond.size,Expr.size]; omega),currentFrame rr hσ (by decide),?_⟩
        simp only [BestCutIndex.next,if_neg (show ¬(valid i ∧ value i<value j) from fun h => hbetter h.2),Matches]
        exact ⟨(rc.frame_var _ (by decide)).trans holdσ.1,(rc.frame_var _ (by decide)).trans holdσ.2.1,
          RamRoundingConstants.storedFrame rc holdσ.2.2 (by decide) (by decide)⟩
  · have hvalid : σ.vars "cut.valid"=0 := by simpa only [if_neg hv] using hσ.2.1
    have hc : (Cond.eq (.var "cut.valid") (.lit 1)).evalB B σ=some false := by
      rw [evalB_condEq (evalB_var (hvalid ▸ (by omega : 0<B))) (evalB_lit h1),hvalid]
      rfl
    refine ⟨σ,(Run.ite_false (c := choose) hc Run.skip).mono (by dsimp [Cond.size,Expr.size]; omega),hσ,?_⟩
    cases old <;> simpa only [BestCutIndex.next,hv,if_false,false_and] using holdσ

end Lax455465Proofs.RamBestUpdate
