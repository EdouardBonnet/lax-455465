import Lax455465Proofs.RamRegionGuard
import Lax455465Proofs.RegionRuntimeProgress
import Mathlib.Logic.Function.Iterate

set_option maxRecDepth 8192
namespace Lax455465Proofs.RamRegionScan
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamRegionInvariant
open RegionRuntimeState RamRegionState RegionRuntimeProgress Lax455465.RationalEncoding
open scoped NNRat

def Invariant {n : ℕ} (I : RationalInstance n) (length : MetricMatrix.Matrix n)
    (seed beta delta threshold : ℚ≥0) (p : ℕ) (start : State n) (σ : Env) : Prop :=
  Fixed I length seed beta delta threshold p σ ∧ Room n p σ ∧ σ.vars "loop.i"≤p+1 ∧
    σ.vars "loop.limit"=p+1 ∧
    View I length seed beta ((advance I length seed beta delta threshold p)^[σ.vars "loop.i"] start) σ

def command : Com := .seq (.assign "loop.i" (.lit 0))
  (.while (.lt (.var "loop.i") (.var "loop.limit")) RamRegionLoop.step)

set_option maxHeartbeats 4800000 in
/-- Execute the actual bounded region loop. Each iteration is justified by
the native residual execution theorem; its preserved state view follows the
exact deterministic transition, while its logical support budget stays fixed. -/
theorem command_spec (B K : ℕ) {n : ℕ} (I : RationalInstance n) (length : MetricMatrix.Matrix n)
    (seed beta delta threshold : ℚ≥0) (p : ℕ) (start : State n) (h2 : 2<B) (hcount : p+1<B)
    (hbeta : (beta : ℚ)=RegionSearch.slope (RegionBudget.steps p) delta) (hdiag : ∀ v, length v v=0)
    (hbound : SupportBound I p start)
    (hbody : ∀ s : State n, SupportBound I p s → s.status=.running →
      Spec B (fun σ => Fixed I length seed beta delta threshold p σ ∧ Dynamic s.active s.history σ ∧ Room n p σ)
        RamRegionLoop.iteration (fun _ τ => Fixed I length seed beta delta threshold p τ ∧ Room n p τ ∧
          RamRegionCore.Output I length seed beta delta threshold p s.active s.history τ) K) :
    Spec B (fun σ => Fixed I length seed beta delta threshold p σ ∧ Room n p σ ∧
      σ.vars "loop.limit"=p+1 ∧ View I length seed beta start σ)
      command (fun _ τ => Fixed I length seed beta delta threshold p τ ∧ Room n p τ ∧
        View I length seed beta ((advance I length seed beta delta threshold p)^[p+1] start) τ)
      ((K+13)*(p+1)+6) := by
  let f := advance I length seed beta delta threshold p
  have hb : ∀ i : ℕ, SupportBound I p (f^[i] start) := by
    intro i
    induction i with
    | zero => simpa using hbound
    | succ i ih =>
      rw [Function.iterate_succ_apply']
      exact advance_bound I length seed beta delta threshold p _ hbeta hdiag ih
  have hstep : Spec B (fun σ => Invariant I length seed beta delta threshold p start σ ∧ σ.vars "loop.i"<p+1)
      RamRegionLoop.step (fun σ τ => Invariant I length seed beta delta threshold p start τ ∧
        τ.vars "loop.i"=σ.vars "loop.i"+1) (K+9) := by
    rintro σ ⟨⟨hf,hr,hi,hlim,hview⟩,hlt⟩
    let i := σ.vars "loop.i"
    let s := f^[i] start
    obtain ⟨ν,rg,pg⟩ := RamRegionGuard.guard_spec B K I length seed beta delta threshold p s h2 hbeta
      (hbody s (hb i)) σ ⟨hf,hr,hview⟩
    have hiν : ν.vars "loop.i"=i := (rg.frame_var _ (by decide)).trans rfl
    have hnext : i+1<B := by dsimp [i]; omega
    let τ := ν.setVar "loop.i" (i+1)
    have ri : Run B (.assign "loop.i" (.add (.var "loop.i") (.lit 1))) ν τ 4 :=
      Run.assign (evalB_bin (op := .add)
        (by rw [evalB_var_iff]; exact ⟨hiν.symm,hiν ▸ (by omega : i<B)⟩) (evalB_lit (by omega)) hnext)
    have rr := rg.seq ri
    refine ⟨τ,by simpa only [RamRegionLoop.step,RamRegionGuard.command] using rr,?_,by simp [τ,i]⟩
    refine ⟨Fixed.frame ri pg.1 (by dsimp [names]; decide) (by dsimp [arrays]; decide),Room.frame ri pg.2.1,
      by simp [τ]; dsimp [i]; omega,
      ((rg.seq ri).frame_var _ (by decide)).trans hlim,?_⟩
    have hv := RamRegionGuard.View.frameCounter ri pg.2.2
    simpa only [τ,vars_setVar,if_true,Function.iterate_succ_apply',f,s] using hv
  have hs := Spec.forRangeZero "loop.i" "loop.limit" (Invariant I length seed beta delta threshold p start)
    (p+1) (K+9) hcount (fun _ h => h.2.2.1) (fun _ h => h.2.2.2.1) hstep
  rintro σ ⟨hf,hr,hlimit,hv⟩
  have rz : Run B (.assign "loop.i" (.lit 0)) σ (σ.setVar "loop.i" 0) 2 := Run.assign (evalB_lit (by omega))
  have hinit : Invariant I length seed beta delta threshold p start (σ.setVar "loop.i" 0) :=
    ⟨Fixed.frame rz hf (by dsimp [names]; decide) (by dsimp [arrays]; decide),Room.frame rz hr,
      by simp,(rz.frame_var _ (by decide)).trans hlimit,
      by simpa only [vars_setVar,if_true,Function.iterate_zero,Function.id_def] using RamRegionGuard.View.frameCounter rz hv⟩
  obtain ⟨τ,rr,pr⟩ := hs σ hinit
  exact ⟨τ,by simpa only [command] using rr,pr.1.1,pr.1.2.1,
    by simpa only [pr.2] using pr.1.2.2.2.2⟩

end Lax455465Proofs.RamRegionScan
