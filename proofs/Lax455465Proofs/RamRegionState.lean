import Lax455465Proofs.RamRegionCore
import Lax455465Proofs.RegionRuntimeState

set_option backward.isDefEq.respectTransparency false
namespace Lax455465Proofs.RamRegionState
open Lax808846Proofs.Imp RamVirtualState RamRegionInvariant RamRegionRecord RegionRuntimeState
open Lax455465.RationalEncoding
open scoped NNRat

def View {n : ℕ} (I : RationalInstance n) (length : MetricMatrix.Matrix n) (seed beta : ℚ≥0)
    (s : State n) (σ : Env) : Prop :=
  match s.status with
  | .running => Dynamic s.active s.history σ
  | .large e => σ.vars "region.phase"=1 ∧
      RamSmallRegion.Input (RadiusSearchData.atRadius (RegionExecutionData.query I length s.active e.root seed beta) e.radius)
        s.active s.history e.root σ
  | .exhausted => σ.vars "region.phase"=2 ∧ Prefix (words s.history) "region.history" σ ∧
      σ.vars "history.pos"=4*s.history.length ∧
      Prefix (RamUnsignedBuffer.encode (MaskedMassData.flags (ResidualData.mask s.active))) "region.active" σ
  | .failed => False

/-- The full native iteration postcondition is the exact next deterministic
state, including the canonical recorded radius and chosen orientation. -/
theorem output_advance {n : ℕ} (I : RationalInstance n) (length : MetricMatrix.Matrix n)
    (seed beta delta threshold : ℚ≥0) (p : ℕ) (s : State n) (σ : Env)
    (hrunning : s.status=.running) (hbeta : (beta : ℚ)=RegionSearch.slope (RegionBudget.steps p) delta)
    (houtput : RamRegionCore.Output I length seed beta delta threshold p s.active s.history σ) :
    View I length seed beta (advance I length seed beta delta threshold p s) σ := by
  cases hroot : RegionSelection.chooseRoot (RegionLoop.weights I s.active) with
  | none =>
    simpa only [advance,hrunning,hroot,View,RamRegionCore.Output] using houtput
  | some root =>
    obtain ⟨r,hs,hb⟩ : ∃ r : ℚ≥0,
        RegionSearch.search (RegionLoop.capacity I s.active) (MetricMatrix.rational length)
          (fun v => (length root v : ℚ)) (fun v => (length v root : ℚ)) seed delta p
          (RegionLoop.chooseDirection I (MetricMatrix.rational length) s.active root)=some (r : ℚ) ∧
        RamRegionBranch.Output (RadiusSearchData.atRadius (RegionExecutionData.query I length s.active root seed beta) r)
          threshold s.active s.history root σ := by
      simpa only [RamRegionCore.Output,hroot] using houtput
    have hr := radius_of_search I length seed beta delta p s.active root r hbeta hs
    let q := RadiusSearchData.atRadius (RegionExecutionData.query I length s.active root seed beta) r
    change RamRegionBranch.Output q threshold s.active s.history root σ at hb
    by_cases hl : RamRegionBranch.large q threshold
    · have ha : advance I length seed beta delta threshold p s=
          {s with status := .large (RamSmallRegion.selected q root)} := by
        simp only [advance,hrunning,hroot,hr]
        change (if RamRegionBranch.large q threshold then _ else _)=_
        rw [if_pos hl]
      rw [ha]
      change σ.vars "region.phase"=1 ∧ RamSmallRegion.Input q s.active s.history root σ
      simpa only [RamRegionBranch.Output,hl,if_true] using hb
    · have ha : advance I length seed beta delta threshold p s=
          {active := s.active \ (RamSmallRegion.selected q root).region.ball (MetricMatrix.rational length),
            history := s.history++[RamSmallRegion.selected q root],status := .running} := by
        simp only [advance,hrunning,hroot,hr]
        change (if RamRegionBranch.large q threshold then _ else _)=_
        rw [if_neg hl]
      rw [ha]
      simp only [RamRegionBranch.Output,hl,if_false] at hb
      change Dynamic (s.active \ (RamSmallRegion.selected q root).region.ball (MetricMatrix.rational length))
        (s.history++[RamSmallRegion.selected q root]) σ
      refine ⟨hb.1,?_,hb.2.2.1,by simpa using hb.2.2.2.1⟩
      simpa only [q,RadiusSearchData.atRadius,RegionExecutionData.query,RamRegionSetup.query] using hb.2.2.2.2

end Lax455465Proofs.RamRegionState
