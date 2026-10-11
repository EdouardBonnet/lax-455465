import Lax455465Proofs.RegionHistory

open scoped BigOperators

namespace Lax455465Proofs.HistoryCharging

open Lax455465.RationalEncoding RegionLoop RegionHistory RegionFrontier RegionOrdering RegionVolume

def cost {n : ℕ} (I : RationalInstance n) (d : RationalDistances.Distance n)
    (history : List (Region n)) (j : ℕ) : ℚ :=
  weight (RegionLoop.capacity I (activeAt d Finset.univ history j)) d

def volume {n : ℕ} (I : RationalInstance n) (d : RationalDistances.Distance n)
    (seed : ℚ) (history : List (Region n)) (j : ℕ) : ℚ :=
  if hj : j < history.length then
    let R := history[j]
    let A := activeAt d Finset.univ history j
    RegionSearch.selectedVolume (RegionLoop.capacity I A) d (d R.root) (fun v => d v R.root)
      seed (chooseDirection I d A R.root) R.radius
  else 0

def boundary {n : ℕ} (I : RationalInstance n) (d : RationalDistances.Distance n)
    (history : List (Region n)) (j : ℕ) : ℚ :=
  if hj : j < history.length then
    let R := history[j]
    orientedBoundary (RegionLoop.capacity I (activeAt d Finset.univ history j)) (R.ball d) R.outward
  else 0

theorem chosen_ball_eq {n : ℕ} (I : RationalInstance n) (d : RationalDistances.Distance n)
    (seed delta : ℚ) (p : ℕ) (A : Finset (Fin n)) (R : Region n)
    (hstep : StepGood I d seed delta p A R) :
    RegionCharging.chosenBall (d R.root) (fun v => d v R.root) (chooseDirection I d A R.root) R.radius =
      R.ball d := by
  unfold RegionCharging.chosenBall Region.ball
  rw [← hstep.2.2.2.1]

theorem volume_bound {n : ℕ} (I : RationalInstance n) (d : RationalDistances.Distance n)
    (seed delta : ℚ) (p : ℕ) (history : List (Region n))
    (hvalid : ValidHistory I d seed delta p Finset.univ history)
    (hd : RationalDistances.Nonnegative d) (j : ℕ) (hj : j < history.length) :
    volume I d seed history j ≤ seed + (cost I d history j - cost I d history (j + 1)) := by
  have hstep := step_valid I d seed delta p history Finset.univ hvalid j hj
  have hb := RegionCharging.selected_volume_bound
    (RegionLoop.capacity I (activeAt d Finset.univ history j)) d
    (d history[j].root) (fun v => d v history[j].root) seed history[j].radius
    (chooseDirection I d (activeAt d Finset.univ history j) history[j].root)
    (capacity_nonnegative I _) hd
  rw [chosen_ball_eq I d seed delta p _ _ hstep, ← capacity_remove,
    ← activeAt_step d history Finset.univ j hj] at hb
  simpa only [volume, dif_pos hj, cost] using hb

theorem boundary_bound {n : ℕ} (I : RationalInstance n) (d : RationalDistances.Distance n)
    (seed delta : ℚ) (p : ℕ) (history : List (Region n))
    (hvalid : ValidHistory I d seed delta p Finset.univ history) (j : ℕ) (hj : j < history.length) :
    boundary I d history j ≤ RegionSearch.slope (RegionBudget.steps p) delta * volume I d seed history j := by
  have hstep := step_valid I d seed delta p history Finset.univ hvalid j hj
  have hb := hstep.2.2.2.2.1
  unfold RegionSearch.Good at hb
  rw [selected_boundary, chosen_ball_eq I d seed delta p _ _ hstep, ← hstep.2.2.2.1] at hb
  simpa only [boundary, volume, dif_pos hj] using hb

theorem charge_eq {n : ℕ} (I : RationalInstance n) (d : RationalDistances.Distance n)
    (history : List (Region n)) (j : Fin history.length) :
    chargedBoundary (fun u v => (I.capacity u v : ℚ)) (index d history) (orientation history) j =
      boundary I d history j.val := by
  rw [charged_eq_boundary _ _ _ j (history[j.val].ball d)
    (fun v ha => frontier d history j.val j.isLt v ha)]
  rw [← capacity_eq_residual I d history j.val j.isLt.le, orientation_eq history j.val j.isLt]
  simp only [boundary, dif_pos j.isLt]

theorem initial_cost {n : ℕ} (I : RationalInstance n) (d : RationalDistances.Distance n)
    (history : List (Region n)) :
    cost I d history 0 = weight (fun u v => (I.capacity u v : ℚ)) d := by
  have hc : RegionLoop.capacity I Finset.univ = (fun u v => (I.capacity u v : ℚ)) := by
    funext u v
    simp only [RegionLoop.capacity, Finset.mem_univ, and_self, ↓reduceIte]
  rw [cost, activeAt_zero, hc]

/-- The complete region history connects the label charges to the
actual search bounds and the telescoped residual costs. -/
theorem total_charge {n : ℕ} (I : RationalInstance n) (d : RationalDistances.Distance n)
    (delta : ℚ) (p : ℕ) (history : List (Region n))
    (hp : 0 < p) (hlen : history.length ≤ p) (hdelta : 0 < delta)
    (hd : RationalDistances.Nonnegative d)
    (hvalid : ValidHistory I d (weight (fun u v => (I.capacity u v : ℚ)) d / p) delta p Finset.univ history) :
    (∑ j : Fin history.length, chargedBoundary (fun u v => (I.capacity u v : ℚ))
      (index d history) (orientation history) j) ≤
      2 * RegionSearch.slope (RegionBudget.steps p) delta * weight (fun u v => (I.capacity u v : ℚ)) d := by
  simp_rw [charge_eq]
  rw [Fin.sum_univ_eq_sum_range]
  have h := RegionCharging.total_boundary_normalized (cost I d history) (boundary I d history)
    (volume I d (weight (fun u v => (I.capacity u v : ℚ)) d / p) history) history.length p
    (RegionSearch.slope (RegionBudget.steps p) delta) hp hlen (by unfold RegionSearch.slope; positivity)
    (by rw [initial_cost]; exact RegionCharging.weight_nonnegative _ d (fun u v => NNRat.coe_nonneg _) hd)
    (RegionCharging.weight_nonnegative _ d (capacity_nonnegative I _) hd)
    (fun j hj => by rw [initial_cost]; exact volume_bound I d _ delta p history hvalid hd j hj)
    (boundary_bound I d _ delta p history hvalid)
  rw [initial_cost] at h
  exact h

end Lax455465Proofs.HistoryCharging
