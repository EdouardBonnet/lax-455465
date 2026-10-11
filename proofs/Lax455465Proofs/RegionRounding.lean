import Lax455465Proofs.HistoryCharging

open scoped BigOperators

namespace Lax455465Proofs.RegionRounding

open Lax455465.RationalEncoding RegionLoop RegionHistory CutSweeps RationalDistances

def supportSize {n : ℕ} (I : RationalInstance n) : ℕ := (RegionSelection.support (weights I Finset.univ)).card

def metricCost {n : ℕ} (I : RationalInstance n) (d : Distance n) : ℚ :=
  RegionVolume.weight (fun u v => (I.capacity u v : ℚ)) d

def radiusBudget {n : ℕ} (I : RationalInstance n) : ℚ := 1 / (4 * LargeBallRounding.total I ^ 2)

def inner {n : ℕ} (d : Distance n) (R : Region n) : Finset (Fin n) :=
  insert R.root (RegionCharging.ball (fun v => d v R.root) R.radius)

def outer {n : ℕ} (d : Distance n) (R : Region n) : Finset (Fin n) :=
  insert R.root (RegionCharging.ball (d R.root) R.radius)

/-- Root insertion ensures that this branch is a total computable function.
On a successful search, insertion leaves both strict balls unchanged. -/
def largeRound {n : ℕ} (I : RationalInstance n) (d : Distance n) (R : Region n) : Option (Finset (Fin n)) :=
  LargeBallRounding.round I d (inner d R) (outer d R)
    ⟨R.root, Finset.mem_insert_self _ _⟩ ⟨R.root, Finset.mem_insert_self _ _⟩

def positiveRound {n : ℕ} (I : RationalInstance n) (d : Distance n) : Option (Finset (Fin n)) :=
  (run I d (metricCost I d / supportSize I) (radiusBudget I) (supportSize I) (supportSize I) Finset.univ).bind
    fun result => match result with
    | .large R => largeRound I d R
    | .regions history => BalancedRegionCut.round I (index d history) (orientation history)

theorem largeRound_correct {n : ℕ} (I : RationalInstance n) (d : Distance n) (R : Region n)
    (hM : 0 < LargeBallRounding.total I) (hd : Nonnegative d) (hdiag : ∀ v, d v v = 0)
    (hsep : 1 ≤ LargeBallRounding.distanceSeparation I d) (htri : ∀ u v w, d u w ≤ d u v + d v w)
    (hlarge : LargeGood I d (radiusBudget I) R) :
    ∃ S, largeRound I d R = some S ∧ admissibleQ I S ∧ ratioQ I S ≤ 6 * metricCost I d := by
  have hin : inner d R = RegionCharging.ball (fun v => d v R.root) R.radius := by
    apply Finset.insert_eq_of_mem
    simp [RegionCharging.ball, hdiag, hlarge.1]
  have hout : outer d R = RegionCharging.ball (d R.root) R.radius := by
    apply Finset.insert_eq_of_mem
    simp [RegionCharging.ball, hdiag, hlarge.1]
  exact LargeBallRounding.round_correct I d (inner d R) (outer d R) _ _ R.root hM hd hdiag hsep htri
    (fun s hs => by
      rw [hin] at hs
      exact ((Finset.mem_filter.mp hs).2.le).trans hlarge.2.1)
    (fun t ht => by
      rw [hout] at ht
      exact ((Finset.mem_filter.mp ht).2.le).trans hlarge.2.1)
    (by rw [hin]; exact hlarge.2.2.2)
    (by rw [hout]; exact hlarge.2.2.1)

/-- Both actual region-growing branches return a positive-demand rational
cut with a uniform finite logarithmic-budget approximation bound. -/
theorem positiveRound_correct {n : ℕ} (I : RationalInstance n) (d : Distance n)
    (hM : 0 < LargeBallRounding.total I) (hp : 2 ≤ supportSize I)
    (hd : Nonnegative d) (hdiag : ∀ v, d v v = 0)
    (hsep : 1 ≤ LargeBallRounding.distanceSeparation I d) (htri : ∀ u v w, d u w ≤ d u v + d v w)
    (hW : 0 < metricCost I d) :
    ∃ S, positiveRound I d = some S ∧ admissibleQ I S ∧
      ratioQ I S ≤ (288 / 5 : ℚ) * (RegionBudget.steps (supportSize I) : ℚ) * metricCost I d := by
  have hp0 : 0 < supportSize I := by omega
  have hpq : (0 : ℚ) < supportSize I := by exact_mod_cast hp0
  have hdelta : 0 < radiusBudget I := by unfold radiusBudget; positivity
  have hseed : 0 < metricCost I d / supportSize I := div_pos hW hpq
  have hcost : metricCost I d ≤ (supportSize I : ℚ) * (metricCost I d / supportSize I) := by
    rw [mul_div_cancel₀ _ (ne_of_gt hpq)]
  obtain ⟨result, hrun, hvalid⟩ := run_correct I d (metricCost I d / supportSize I) (radiusBudget I)
    (supportSize I) (supportSize I) hd hdiag htri hseed hdelta hp0 hcost Finset.univ le_rfl
  cases result with
  | large R =>
    obtain ⟨S, hs, hadm, hratio⟩ := largeRound_correct I d R hM hd hdiag hsep htri hvalid
    refine ⟨S, by simp only [positiveRound, hrun, Option.bind_some, hs], hadm, hratio.trans ?_⟩
    have hk : (1 : ℚ) ≤ RegionBudget.steps (supportSize I) := by
      exact_mod_cast RegionBudget.steps_pos (supportSize I)
    have hmul := mul_le_mul_of_nonneg_right hk hW.le
    nlinarith
  | regions history =>
    have hc := HistoryCharging.total_charge I d (radiusBudget I) (supportSize I) history hp0 hvalid.2 hdelta hd hvalid.1
    have heq : 2 * RegionSearch.slope (RegionBudget.steps (supportSize I)) (radiusBudget I) * metricCost I d =
        8 * (RegionBudget.steps (supportSize I) : ℚ) * BalancedRegionCut.total I ^ 2 * metricCost I d := by
      unfold RegionSearch.slope radiusBudget
      change 2 * ((RegionBudget.steps (supportSize I) : ℚ) / (1 / (4 * LargeBallRounding.total I ^ 2))) * metricCost I d =
        8 * (RegionBudget.steps (supportSize I) : ℚ) * LargeBallRounding.total I ^ 2 * metricCost I d
      field_simp [ne_of_gt hM]
      ring
    change (∑ j : Fin history.length, RegionOrdering.chargedBoundary (fun u v => (I.capacity u v : ℚ))
      (index d history) (orientation history) j) ≤
        2 * RegionSearch.slope (RegionBudget.steps (supportSize I)) (radiusBudget I) * metricCost I d at hc
    rw [heq] at hc
    obtain ⟨S, hs, hadm, hratio⟩ := BalancedRegionCut.round_ratio I (index d history) (orientation history)
      (RegionBudget.steps (supportSize I)) (metricCost I d) hM (Nat.cast_nonneg _) hW.le
      (blocks_small I d _ _ _ history hvalid.1 hM) hc
    exact ⟨S, by simp only [positiveRound, hrun, Option.bind_some, hs], hadm, hratio⟩

end Lax455465Proofs.RegionRounding
