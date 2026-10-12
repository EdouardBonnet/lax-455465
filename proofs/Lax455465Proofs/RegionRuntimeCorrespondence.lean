import Lax455465Proofs.RegionRuntimeTermination
import Lax455465Proofs.RamRoundingInit

set_option backward.isDefEq.respectTransparency false
open scoped BigOperators NNRat
namespace Lax455465Proofs.RegionRuntimeCorrespondence
open Lax455465.RationalEncoding RegionRuntimeState RamRegionRecord RegionLoop

def outcome {n : ℕ} (s : State n) : Option (Result n) :=
  match s.status with
  | .large e => some (.large e.region)
  | .exhausted => some (.regions (s.history.map Entry.region))
  | _ => none

def finish {n : ℕ} (history : List (Entry n)) (result : Result n) : Result n :=
  match result with
  | .large R => .large R
  | .regions rest => .regions (history.map Entry.region++rest)

theorem coe_total {n : ℕ} (I : RationalInstance n) :
    (RamRoundingInit.total I.weight : ℚ)=LargeBallRounding.total I := by
  simp [RamRoundingInit.total,LargeBallRounding.total,List.sum_ofFn,NNRat.cast_sum]

theorem entry_region {n : ℕ} (I : RationalInstance n) (length : MetricMatrix.Matrix n)
    (active : Finset (Fin n)) (root : Fin n) (seed beta r : ℚ≥0) :
    (RamSmallRegion.selected (RadiusSearchData.atRadius (RegionExecutionData.query I length active root seed beta) r) root).region=
      ⟨root,(r : ℚ),chooseDirection I (MetricMatrix.rational length) active root r⟩ := by
  unfold RamSmallRegion.selected Entry.region
  simp only [RadiusSearchData.atRadius,RegionExecutionData.query,RamRegionSetup.query,
    RegionQueryData.direction,ResidualData.rational_weights,chooseDirection]
  rfl

theorem frozen_iterate {n : ℕ} (I : RationalInstance n) (length : MetricMatrix.Matrix n)
    (seed beta delta threshold : ℚ≥0) (p k : ℕ) (s : State n) (h : s.status≠.running) :
    (advance I length seed beta delta threshold p)^[k] s=s := by
  have hf : advance I length seed beta delta threshold p s=s := by
    cases hs : s.status <;> simp_all [advance]
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply',ih,hf]

set_option maxHeartbeats 2400000 in
/-- The bounded imperative state's recorded regions and large-ball witness
are exactly the mathematical region loop's result. -/
theorem run_eq {n : ℕ} (I : RationalInstance n) (length : MetricMatrix.Matrix n)
    (seed beta delta : ℚ≥0) (p fuel : ℕ) (active : Finset (Fin n)) (history : List (Entry n))
    (hbeta : (beta : ℚ)=RegionSearch.slope (RegionBudget.steps p) delta)
    (hseed : 0<(seed : ℚ)) (hdelta : 0<(delta : ℚ)) (hp : 0<p)
    (hdiag : ∀ v, length v v=0)
    (htri : ∀ u v w, (length u w : ℚ)≤(length u v : ℚ)+(length v w : ℚ))
    (hcost : RegionRounding.metricCost I (MetricMatrix.rational length)≤(p : ℚ)*(seed : ℚ))
    (hfuel : (RegionSelection.support (weights I active)).card≤fuel) :
    outcome ((advance I length seed beta delta (RamLargeThreshold.threshold (RamRoundingInit.total I.weight)) p)^[fuel+1]
      ⟨active,history,.running⟩)=
      (run I (MetricMatrix.rational length) seed delta p fuel active).map (finish history) := by
  let threshold := RamLargeThreshold.threshold (RamRoundingInit.total I.weight)
  let f := advance I length seed beta delta threshold p
  induction fuel generalizing active history with
  | zero =>
    have hn : RegionSelection.chooseRoot (weights I active)=none :=
      (root_none_iff _).mpr (by omega)
    simp only [Nat.zero_add,Function.iterate_one,advance,hn,run,outcome,finish,
      Option.map_some,List.nil_append,List.append_nil,if_true]
  | succ fuel ih =>
    cases hroot : RegionSelection.chooseRoot (weights I active) with
    | none =>
      have ha : f ⟨active,history,.running⟩=⟨active,history,.exhausted⟩ := by simp [f,advance,hroot]
      dsimp only [f,threshold] at ha
      rw [Function.iterate_succ_apply,ha]
      rw [frozen_iterate I length seed beta delta threshold p (fuel+1) ⟨active,history,.exhausted⟩ (by intro h; cases h)]
      simp only [run,hroot,outcome,finish,Option.map_some,List.append_nil]
    | some root =>
      obtain ⟨rQ,hsQ⟩ := RegionExecutionData.search_exists I length active root seed delta p hseed hdelta hp htri hcost
      have hc := radius_coe I length seed beta delta p active root hbeta
      cases hr : radius I length seed beta delta p active root with
      | none => rw [hr,Option.map_none,hsQ] at hc; cases hc
      | some r =>
        have hs : RegionSearch.search (capacity I active) (MetricMatrix.rational length)
            (fun v => (length root v : ℚ)) (fun v => (length v root : ℚ)) seed delta p
            (chooseDirection I (MetricMatrix.rational length) active root)=some (r : ℚ) := by
          simpa only [hr,Option.map_some] using hc.symm
        have hsRun : RegionSearch.search (capacity I active) (MetricMatrix.rational length)
            (MetricMatrix.rational length root) (fun v => MetricMatrix.rational length v root) seed delta p
            (chooseDirection I (MetricMatrix.rational length) active root)=some (r : ℚ) := by
          dsimp only [MetricMatrix.rational] at hs ⊢
          exact hs
        let q := RadiusSearchData.atRadius (RegionExecutionData.query I length active root seed beta) r
        let e := RamSmallRegion.selected q root
        let R : Region n := ⟨root,(r : ℚ),chooseDirection I (MetricMatrix.rational length) active root r⟩
        have he : e.region=R := entry_region I length active root seed beta r
        have hlarge : RamRegionBranch.large q threshold ↔
            (2/3 : ℚ)*LargeBallRounding.total I≤∑ v∈R.ball (MetricMatrix.rational length), weights I active v := by
          have h := RegionExecutionData.large_iff I length active root seed beta r (RamRoundingInit.total I.weight)
          rw [coe_total] at h
          have heR : RegionExecutionData.region q root=R := by
            exact (show RegionExecutionData.region q root=e.region from rfl).trans he
          change RamRegionBranch.large q threshold ↔
            (2/3 : ℚ)*LargeBallRounding.total I≤∑ v∈(RegionExecutionData.region q root).ball (MetricMatrix.rational length), weights I active v at h
          rw [heR] at h
          exact h
        have hrun : run I (MetricMatrix.rational length) seed delta p (fuel+1) active=
            if (2/3 : ℚ)*LargeBallRounding.total I≤∑ v∈R.ball (MetricMatrix.rational length), weights I active v then
              some (.large R)
            else (run I (MetricMatrix.rational length) seed delta p fuel (active \ R.ball (MetricMatrix.rational length))).map
              (fun result => match result with
                | .large T => .large T
                | .regions rest => .regions (R::rest)) := by
          simp only [run,hroot,hsRun]
          rfl
        by_cases hl : RamRegionBranch.large q threshold
        · have ha : f ⟨active,history,.running⟩=⟨active,history,.large e⟩ := by
            simp only [f,advance,hroot,hr]
            change (if RamRegionBranch.large q threshold then _ else _)=_
            rw [if_pos hl]
          dsimp only [f,threshold] at ha
          rw [Function.iterate_succ_apply,ha]
          rw [frozen_iterate I length seed beta delta threshold p (fuel+1) ⟨active,history,.large e⟩ (by intro h; cases h)]
          have hlQ := hlarge.mp hl
          rw [hrun,if_pos hlQ]
          simp only [outcome,finish,Option.map_some,he]
        · have hsmall : ¬(2/3 : ℚ)*LargeBallRounding.total I≤∑ v∈R.ball (MetricMatrix.rational length), weights I active v :=
            mt hlarge.mpr hl
          have ha : f ⟨active,history,.running⟩=
              ⟨active \ R.ball (MetricMatrix.rational length),history++[e],.running⟩ := by
            simp only [f,advance,hroot,hr]
            change (if RamRegionBranch.large q threshold then _ else _)=_
            rw [if_neg hl,he]
          have hrootPos : 0<weights I active root := by simpa only [decide_eq_true_eq] using List.find?_some hroot
          have hprogress : (RegionSelection.support (weights I (active \ R.ball (MetricMatrix.rational length)))).card<
              (RegionSelection.support (weights I active)).card := by
            rw [weights_remove]
            apply RegionSelection.support_decreases _ _ root hrootPos
            have hrad := RegionSearch.search_radius (capacity I active) (MetricMatrix.rational length)
              (fun v => (length root v : ℚ)) (fun v => (length v root : ℚ)) seed delta p
              (chooseDirection I (MetricMatrix.rational length) active root) r hdelta.le hs
            have hrpos : 0<r := by exact_mod_cast hrad.1
            unfold R Region.ball
            cases hd : chooseDirection I (MetricMatrix.rational length) active root r <;>
              simp [RegionCharging.ball,hd,MetricMatrix.rational,hdiag,hrad.1,hrpos]
          dsimp only [f,threshold] at ha
          rw [Function.iterate_succ_apply,ha]
          rw [ih (active \ R.ball (MetricMatrix.rational length)) (history++[e]) (by omega)]
          rw [hrun,if_neg hsmall]
          simp only [Option.map_map]
          apply congrArg (fun g => (run I (MetricMatrix.rational length) seed delta p fuel (active \ R.ball (MetricMatrix.rational length))).map g)
          funext result
          cases result <;> simp [finish,Function.comp_def,List.map_append,he,List.append_assoc]

def ValidFinal {n : ℕ} (I : RationalInstance n) (length : MetricMatrix.Matrix n)
    (seed delta : ℚ≥0) (p : ℕ) (s : State n) : Prop :=
  match s.status with
  | .large e => LargeGood I (MetricMatrix.rational length) delta e.region
  | .exhausted => ValidHistory I (MetricMatrix.rational length) seed delta p Finset.univ
      (s.history.map Entry.region) ∧ s.history.length≤p
  | _ => False

/-- The native loop's exact final state carries the mathematical large-ball
or valid exhausted-history guarantees used by deterministic cut rounding. -/
theorem final_correct {n : ℕ} (I : RationalInstance n) (length : MetricMatrix.Matrix n)
    (seed beta delta : ℚ≥0) (p : ℕ)
    (hbeta : (beta : ℚ)=RegionSearch.slope (RegionBudget.steps p) delta)
    (hseed : 0<(seed : ℚ)) (hdelta : 0<(delta : ℚ)) (hp : 0<p)
    (hdiag : ∀ v, length v v=0)
    (htri : ∀ u v w, (length u w : ℚ)≤(length u v : ℚ)+(length v w : ℚ))
    (hcost : RegionRounding.metricCost I (MetricMatrix.rational length)≤(p : ℚ)*(seed : ℚ))
    (hsupport : (RegionSelection.support (weights I Finset.univ)).card≤p) :
    ValidFinal I length seed delta p
      ((advance I length seed beta delta (RamLargeThreshold.threshold (RamRoundingInit.total I.weight)) p)^[p+1]
        (RamRegionBoundedLoop.initial n)) := by
  let final := (advance I length seed beta delta (RamLargeThreshold.threshold (RamRoundingInit.total I.weight)) p)^[p+1]
    (RamRegionBoundedLoop.initial n)
  change ValidFinal I length seed delta p final
  have hd : RationalDistances.Nonnegative (MetricMatrix.rational length) := fun u v => (length u v).coe_nonneg
  obtain ⟨result,hr,hvalid⟩ := run_correct I (MetricMatrix.rational length) seed delta p p hd
    (fun v => by simp [MetricMatrix.rational,hdiag]) htri hseed hdelta hp hcost Finset.univ hsupport
  have heq := run_eq I length seed beta delta p p Finset.univ [] hbeta hseed hdelta hp hdiag htri hcost hsupport
  rw [hr,Option.map_some] at heq
  have heq' : outcome final=some result := by
    cases result <;> simpa only [final,RamRegionBoundedLoop.initial,finish,List.map_nil,List.nil_append] using heq
  cases hs : final.status with
  | running => simp only [outcome,hs] at heq'; cases heq'
  | failed => simp only [outcome,hs] at heq'; cases heq'
  | large e =>
    have he : result=.large e.region := by simpa only [outcome,hs,Option.some.injEq] using heq'.symm
    subst result
    simpa only [ValidFinal,hs] using hvalid
  | exhausted =>
    have he : result=.regions (final.history.map Entry.region) := by simpa only [outcome,hs,Option.some.injEq] using heq'.symm
    subst result
    simp only [ValidFinal,hs]
    exact ⟨hvalid.1,(by simpa only [List.length_map] using hvalid.2.trans hsupport)⟩

end Lax455465Proofs.RegionRuntimeCorrespondence
