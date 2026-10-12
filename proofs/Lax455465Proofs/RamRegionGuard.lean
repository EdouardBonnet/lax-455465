import Lax455465Proofs.RamRegionState

set_option maxRecDepth 8192
namespace Lax455465Proofs.RamRegionGuard
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamRegionInvariant
open RegionRuntimeState RamRegionState Lax455465.RationalEncoding
open scoped NNRat

def command : Com := .ite (.eq (.var "region.phase") (.lit 0)) RamRegionLoop.iteration .skip

theorem guard_spec (B K : ℕ) {n : ℕ} (I : RationalInstance n) (length : MetricMatrix.Matrix n)
    (seed beta delta threshold : ℚ≥0) (p : ℕ) (s : State n) (h2 : 2<B)
    (hbeta : (beta : ℚ)=RegionSearch.slope (RegionBudget.steps p) delta)
    (hbody : s.status=.running →
      Spec B (fun σ => Fixed I length seed beta delta threshold p σ ∧ Dynamic s.active s.history σ ∧ Room n p σ)
        RamRegionLoop.iteration (fun _ τ => Fixed I length seed beta delta threshold p τ ∧ Room n p τ ∧
          RamRegionCore.Output I length seed beta delta threshold p s.active s.history τ) K) :
    Spec B (fun σ => Fixed I length seed beta delta threshold p σ ∧ Room n p σ ∧ View I length seed beta s σ)
      command (fun _ τ => Fixed I length seed beta delta threshold p τ ∧ Room n p τ ∧
        View I length seed beta (advance I length seed beta delta threshold p s) τ) (K+5) := by
  rintro σ ⟨hf,hr,hv⟩
  cases hs : s.status with
  | running =>
    have hd : Dynamic s.active s.history σ := by simpa only [View,hs] using hv
    have hc : (Cond.eq (.var "region.phase") (.lit 0)).evalB B σ=some true := by
      rw [evalB_condEq (evalB_var (hd.phase ▸ (by omega : 0<B))) (evalB_lit (by omega)),hd.phase]
      rfl
    obtain ⟨τ,rr,pr⟩ := hbody hs σ ⟨hf,hd,hr⟩
    exact ⟨τ,(Run.ite_true (d := .skip) hc rr).mono (by dsimp [Cond.size,Expr.size]; omega),pr.1,pr.2.1,
      output_advance I length seed beta delta threshold p s τ hs hbeta pr.2.2⟩
  | large e =>
    have hp : σ.vars "region.phase"=1 := (show σ.vars "region.phase"=1 ∧ _ from by simpa only [View,hs] using hv).1
    have hc : (Cond.eq (.var "region.phase") (.lit 0)).evalB B σ=some false := by
      rw [evalB_condEq (evalB_var (hp ▸ (by omega : 1<B))) (evalB_lit (by omega)),hp]
      rfl
    exact ⟨σ,(Run.ite_false (c := RamRegionLoop.iteration) hc Run.skip).mono (by dsimp [Cond.size,Expr.size]; omega),hf,hr,
      by simpa only [advance,hs] using hv⟩
  | exhausted =>
    have hp : σ.vars "region.phase"=2 := (show σ.vars "region.phase"=2 ∧ _ from by simpa only [View,hs] using hv).1
    have hc : (Cond.eq (.var "region.phase") (.lit 0)).evalB B σ=some false := by
      rw [evalB_condEq (evalB_var (hp ▸ h2)) (evalB_lit (by omega)),hp]
      rfl
    exact ⟨σ,(Run.ite_false (c := RamRegionLoop.iteration) hc Run.skip).mono (by dsimp [Cond.size,Expr.size]; omega),hf,hr,
      by simpa only [advance,hs] using hv⟩
  | failed =>
    have : False := by simpa only [View,hs] using hv
    exact this.elim

/-- Advancing the loop counter preserves every field of the typed state
view, including the stored large-ball witness and region history. -/
theorem View.frameCounter {B K : ℕ} {e : Expr} {σ τ : Env}
    (rr : Run B (.assign "loop.i" e) σ τ K)
    {n : ℕ} {I : RationalInstance n} {length : MetricMatrix.Matrix n} {seed beta : ℚ≥0} {s : State n}
    (h : View I length seed beta s σ) : View I length seed beta s τ := by
  cases hs : s.status with
  | running =>
    have hd : Dynamic s.active s.history σ := by simpa only [View,hs] using h
    simpa only [View,hs] using Dynamic.frame rr hd (by dsimp [dynamicNames,Com.wvars,Com.warrs]; decide) (by dsimp [dynamicArrays,Com.wvars,Com.warrs]; decide)
  | large entry =>
    obtain ⟨hp,hi⟩ := (show σ.vars "region.phase"=1 ∧
      RamSmallRegion.Input (RadiusSearchData.atRadius (RegionExecutionData.query I length s.active entry.root seed beta) entry.radius)
        s.active s.history entry.root σ from by simpa only [View,hs] using h)
    simp only [View,hs]
    refine ⟨(rr.frame_var _ (by dsimp [Com.wvars,Com.warrs]; decide)).trans hp,?_,?_,?_,?_,?_⟩
    · refine ⟨RamRegionContext.Input.frame rr hi.masks.input (by dsimp [RamRegionContext.sourceVariables,Com.wvars,Com.warrs]; decide)
        (by dsimp [RamRegionContext.arrays,Com.wvars,Com.warrs]; decide),?_,?_,(rr.frame_var _ (by dsimp [Com.wvars,Com.warrs]; decide)).trans hi.masks.directionValue⟩
      · simpa only [Prefix,rr.frame_arr "region.outMask" (by dsimp [Com.wvars,Com.warrs]; decide)] using hi.masks.outMask
      · simpa only [Prefix,rr.frame_arr "region.inMask" (by dsimp [Com.wvars,Com.warrs]; decide)] using hi.masks.inMask
    · exact (rr.frame_var _ (by dsimp [Com.wvars,Com.warrs]; decide)).trans hi.rootValue
    · simpa only [Prefix,rr.frame_arr "region.active" (by dsimp [Com.wvars,Com.warrs]; decide)] using hi.activeData
    · simpa only [Prefix,rr.frame_arr "region.history" (by dsimp [Com.wvars,Com.warrs]; decide)] using hi.historyData
    · exact (rr.frame_var _ (by dsimp [Com.wvars,Com.warrs]; decide)).trans hi.historyPosition
  | exhausted =>
    have hh : σ.vars "region.phase"=2 ∧ Prefix (RamRegionRecord.words s.history) "region.history" σ ∧
        σ.vars "history.pos"=4*s.history.length ∧
        Prefix (RamUnsignedBuffer.encode (MaskedMassData.flags (ResidualData.mask s.active))) "region.active" σ := by
      simpa only [View,hs] using h
    simp only [View,hs]
    exact ⟨(rr.frame_var _ (by dsimp [Com.wvars,Com.warrs]; decide)).trans hh.1,
      by simpa only [Prefix,rr.frame_arr "region.history" (by dsimp [Com.wvars,Com.warrs]; decide)] using hh.2.1,
      (rr.frame_var _ (by dsimp [Com.wvars,Com.warrs]; decide)).trans hh.2.2.1,
      by simpa only [Prefix,rr.frame_arr "region.active" (by dsimp [Com.wvars,Com.warrs]; decide)] using hh.2.2.2⟩
  | failed =>
    have : False := by simpa only [View,hs] using h
    exact this.elim

end Lax455465Proofs.RamRegionGuard
