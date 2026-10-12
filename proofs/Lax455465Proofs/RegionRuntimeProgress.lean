import Lax455465Proofs.RegionRuntimeState

set_option backward.isDefEq.respectTransparency false
namespace Lax455465Proofs.RegionRuntimeProgress
open Lax455465.RationalEncoding RegionRuntimeState
open scoped NNRat

def SupportBound {n : ℕ} (I : RationalInstance n) (p : ℕ) (s : State n) : Prop :=
  s.history.length+(RegionSelection.support (RegionLoop.weights I s.active)).card≤p

/-- Every successful small region spends one unit of the original support
budget. Inactive and zero-weight vertices cannot create extra iterations. -/
theorem advance_bound {n : ℕ} (I : RationalInstance n) (length : MetricMatrix.Matrix n)
    (seed beta delta threshold : ℚ≥0) (p : ℕ) (s : State n)
    (hbeta : (beta : ℚ)=RegionSearch.slope (RegionBudget.steps p) delta)
    (hdiag : ∀ v, length v v=0) (hbound : SupportBound I p s) :
    SupportBound I p (advance I length seed beta delta threshold p s) := by
  cases hstatus : s.status with
  | large e => simpa only [advance,hstatus] using hbound
  | exhausted => simpa only [advance,hstatus] using hbound
  | failed => simpa only [advance,hstatus] using hbound
  | running =>
    cases hroot : RegionSelection.chooseRoot (RegionLoop.weights I s.active) with
    | none => simpa only [advance,hstatus,hroot,SupportBound] using hbound
    | some root =>
      cases hr : radius I length seed beta delta p s.active root with
      | none => simpa only [advance,hstatus,hroot,hr,SupportBound] using hbound
      | some r =>
        let q := RadiusSearchData.atRadius (RegionExecutionData.query I length s.active root seed beta) r
        let e := RamSmallRegion.selected q root
        by_cases hl : RamRegionBranch.large q threshold
        · have ha : advance I length seed beta delta threshold p s={s with status := .large e} := by
            simp only [advance,hstatus,hroot,hr]
            change (if RamRegionBranch.large q threshold then _ else _)=_
            rw [if_pos hl]
          simpa only [ha,SupportBound] using hbound
        · have ha : advance I length seed beta delta threshold p s=
              {active := s.active \ e.region.ball (MetricMatrix.rational length),history := s.history++[e],status := .running} := by
            simp only [advance,hstatus,hroot,hr]
            change (if RamRegionBranch.large q threshold then _ else _)=_
            rw [if_neg hl]
          have hc := radius_coe I length seed beta delta p s.active root hbeta
          rw [hr,Option.map_some] at hc
          have hrootPos : 0<RegionLoop.weights I s.active root := by
            simpa only [decide_eq_true_eq] using List.find?_some hroot
          have hball : e.region.ball (MetricMatrix.rational length)=RegionCharging.chosenBall
              (fun v => (length root v : ℚ)) (fun v => (length v root : ℚ))
              (RegionLoop.chooseDirection I (MetricMatrix.rational length) s.active root) r := by
            unfold e RamSmallRegion.selected RamRegionRecord.Entry.region RegionLoop.Region.ball RegionCharging.chosenBall
            simp only [q,RadiusSearchData.atRadius,RegionExecutionData.query,RamRegionSetup.query,
              RegionQueryData.direction,ResidualData.rational_weights,RegionLoop.chooseDirection]
            rfl
          have hprogress : (RegionSelection.support (RegionLoop.weights I (s.active \ e.region.ball (MetricMatrix.rational length)))).card<
              (RegionSelection.support (RegionLoop.weights I s.active)).card := by
            rw [RegionLoop.weights_remove,hball]
            exact RegionSelection.search_progress (RegionLoop.capacity I s.active) (MetricMatrix.rational length)
              (RegionLoop.weights I s.active) (fun v => (length root v : ℚ)) (fun v => (length v root : ℚ))
              seed delta p root r hrootPos
              (by rw [hdiag root]; rfl) (by rw [hdiag root]; rfl) delta.coe_nonneg hc.symm
          simp only [ha,SupportBound,List.length_append,List.length_singleton]
          unfold SupportBound at hbound
          omega

end Lax455465Proofs.RegionRuntimeProgress
