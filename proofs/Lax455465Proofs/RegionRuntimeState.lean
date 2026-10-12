import Lax455465Proofs.RegionExecutionData

set_option backward.isDefEq.respectTransparency false
namespace Lax455465Proofs.RegionRuntimeState
open Lax455465.RationalEncoding RegionQueryData RamRegionRecord
open scoped NNRat

inductive Status (n : ℕ) where
  | running
  | large : Entry n → Status n
  | exhausted
  | failed

structure State (n : ℕ) where
  active : Finset (Fin n)
  history : List (Entry n)
  status : Status n

def radius {n : ℕ} (I : RationalInstance n) (length : MetricMatrix.Matrix n)
    (seed beta delta : ℚ≥0) (p : ℕ) (active : Finset (Fin n)) (root : Fin n) : Option ℚ≥0 :=
  (RadiusData.candidates (length root) (fun v => length v root) (RegionBudget.steps p) delta).find?
    (fun r => accepted (RadiusSearchData.atRadius (RegionExecutionData.query I length active root seed beta) r))

theorem radius_coe {n : ℕ} (I : RationalInstance n) (length : MetricMatrix.Matrix n)
    (seed beta delta : ℚ≥0) (p : ℕ) (active : Finset (Fin n)) (root : Fin n)
    (hbeta : (beta : ℚ)=RegionSearch.slope (RegionBudget.steps p) delta) :
    (radius I length seed beta delta p active root).map (fun r : ℚ≥0 => (r : ℚ))=
      RegionSearch.search (RegionLoop.capacity I active) (MetricMatrix.rational length)
        (fun v => (length root v : ℚ)) (fun v => (length v root : ℚ)) seed delta p
        (RegionLoop.chooseDirection I (MetricMatrix.rational length) active root) := by
  have h := RadiusSearchData.search_value (RegionExecutionData.query I length active root seed beta) delta p hbeta
  dsimp only [RegionExecutionData.query,RamRegionSetup.query,RegionQueryData.direction] at h
  unfold RegionQueryData.direction at h
  simp only [ResidualData.rational_capacity,ResidualData.rational_weights] at h
  dsimp only [radius,RegionExecutionData.query,RamRegionSetup.query,RegionLoop.chooseDirection,MetricMatrix.rational] at h ⊢
  unfold MetricMatrix.rational
  exact h

theorem radius_of_search {n : ℕ} (I : RationalInstance n) (length : MetricMatrix.Matrix n)
    (seed beta delta : ℚ≥0) (p : ℕ) (active : Finset (Fin n)) (root : Fin n) (r : ℚ≥0)
    (hbeta : (beta : ℚ)=RegionSearch.slope (RegionBudget.steps p) delta)
    (hs : RegionSearch.search (RegionLoop.capacity I active) (MetricMatrix.rational length)
      (fun v => (length root v : ℚ)) (fun v => (length v root : ℚ)) seed delta p
      (RegionLoop.chooseDirection I (MetricMatrix.rational length) active root)=some (r : ℚ)) :
    radius I length seed beta delta p active root=some r := by
  have h := radius_coe I length seed beta delta p active root hbeta
  rw [hs] at h
  cases hh : radius I length seed beta delta p active root with
  | none => simp only [hh,Option.map_none] at h; cases h
  | some r' =>
    have he : r'=r := NNRat.coe_injective (by simpa only [hh,Option.map_some,Option.some.injEq] using h)
    simpa only [he] using hh

/-- The deterministic runtime state transition, with exactly the native
candidate order and two-thirds branch. Frozen states remain unchanged. -/
def advance {n : ℕ} (I : RationalInstance n) (length : MetricMatrix.Matrix n)
    (seed beta delta threshold : ℚ≥0) (p : ℕ) (s : State n) : State n :=
  match s.status with
  | .running =>
    match RegionSelection.chooseRoot (RegionLoop.weights I s.active) with
    | none => {s with status := .exhausted}
    | some root =>
      match radius I length seed beta delta p s.active root with
      | none => {s with status := .failed}
      | some r =>
        let q := RadiusSearchData.atRadius (RegionExecutionData.query I length s.active root seed beta) r
        let e := RamSmallRegion.selected q root
        if RamRegionBranch.large q threshold then {s with status := .large e}
        else {active := s.active \ e.region.ball (MetricMatrix.rational length),history := s.history++[e],status := .running}
  | _ => s

end Lax455465Proofs.RegionRuntimeState
