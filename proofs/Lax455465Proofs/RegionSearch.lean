import Lax455465Proofs.RegionCell
import Lax455465Proofs.RegionBudget

namespace Lax455465Proofs.RegionSearch

open RegionVolume RegionInterval

/-- Rational grid; no logarithm or real arithmetic is executed. -/
def grid (k : ℕ) (delta : ℚ) (j : ℕ) : ℚ := delta * j / k

def slope (k : ℕ) (delta : ℚ) : ℚ := k / delta

def candidates {n : ℕ} (outDistance inDistance : Fin n → ℚ)
    (k : ℕ) (delta : ℚ) : List ℚ :=
  (List.range k).flatMap fun j =>
    RegionThresholds.candidates outDistance inDistance
      (grid k delta j) (grid k delta (j + 1))

/-- The orientation is computed separately, for example by comparing the
two ball masses. The radius search works for any such choice. -/
def selectedVolume {n : ℕ} (capacity length : Matrix n)
    (outDistance inDistance : Fin n → ℚ) (seed : ℚ) (direction : ℚ → Bool) (r : ℚ) : ℚ :=
  if direction r then volume capacity length outDistance seed r
  else volume (fun u v => capacity v u) (fun u v => length v u) inDistance seed r

def selectedBoundary {n : ℕ} (capacity : Matrix n)
    (outDistance inDistance : Fin n → ℚ) (direction : ℚ → Bool) (r : ℚ) : ℚ :=
  if direction r then boundary capacity outDistance r
  else boundary (fun u v => capacity v u) inDistance r

def Good {n : ℕ} (capacity length : Matrix n)
    (outDistance inDistance : Fin n → ℚ) (seed beta : ℚ) (direction : ℚ → Bool) (r : ℚ) : Prop :=
  selectedBoundary capacity outDistance inDistance direction r ≤
    beta * selectedVolume capacity length outDistance inDistance seed direction r

instance {n : ℕ} (capacity length : Matrix n)
    (outDistance inDistance : Fin n → ℚ) (seed beta : ℚ) (direction : ℚ → Bool) (r : ℚ) :
    Decidable (Good capacity length outDistance inDistance seed beta direction r) :=
  inferInstanceAs (Decidable (_ ≤ _))

/-- First successful threshold in the actual finite candidate list. -/
def search {n : ℕ} (capacity length : Matrix n)
    (outDistance inDistance : Fin n → ℚ) (seed delta : ℚ) (p : ℕ)
    (direction : ℚ → Bool) : Option ℚ :=
  (candidates outDistance inDistance (RegionBudget.steps p) delta).find? fun r =>
    decide (0 < r ∧ Good capacity length outDistance inDistance seed
      (slope (RegionBudget.steps p) delta) direction r)

private theorem grid_zero (k : ℕ) (delta : ℚ) : grid k delta 0 = 0 := by simp [grid]

private theorem grid_last (k : ℕ) (delta : ℚ) (hk : 0 < k) : grid k delta k = delta := by
  have hkq : (k : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  simp [grid, hkq]

private theorem grid_nonneg (k : ℕ) (delta : ℚ) (j : ℕ) (hd : 0 ≤ delta) :
    0 ≤ grid k delta j := by unfold grid; positivity

private theorem grid_mono (k : ℕ) (delta : ℚ) (j : ℕ) (hd : 0 ≤ delta) :
    grid k delta j ≤ grid k delta (j + 1) := by
  unfold grid
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg k)
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.le_succ j) hd

private theorem grid_width (k : ℕ) (delta : ℚ) (j : ℕ)
    (hk : 0 < k) (hd : 0 < delta) :
    (grid k delta (j + 1) - grid k delta j) * slope k delta = 1 := by
  have hkq : (k : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  unfold grid slope
  push_cast
  field_simp [hkq, ne_of_gt hd]
  ring

/-- Every tested radius lies inside the prescribed rational radius budget. -/
theorem candidates_bound {n : ℕ} (outDistance inDistance : Fin n → ℚ)
    (k : ℕ) (delta r : ℚ) (hk : 0 < k) (hd : 0 ≤ delta)
    (hr : r ∈ candidates outDistance inDistance k delta) : 0 ≤ r ∧ r ≤ delta := by
  obtain ⟨j, hj, hrj⟩ := List.mem_flatMap.mp hr
  have hjk : j < k := List.mem_range.mp hj
  have hb := RegionThresholds.bounds outDistance inDistance
    (grid k delta j) (grid k delta (j + 1)) (grid_mono k delta j hd) r
    ((Finset.mem_sort (· ≤ ·)).mp hrj)
  have hlast : grid k delta (j + 1) ≤ grid k delta k := by
    unfold grid
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg k)
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.succ_le_of_lt hjk) hd
  rw [grid_last k delta hk] at hlast
  exact ⟨(grid_nonneg k delta j hd).trans hb.1, hb.2.trans hlast⟩

/-- Some tested positive threshold succeeds: otherwise each grid cell
doubles the product volume, contradicting the finite 4p² budget. -/
theorem exists_good {n : ℕ} (capacity length : Matrix n)
    (outDistance inDistance : Fin n → ℚ) (seed delta : ℚ) (p : ℕ)
    (direction : ℚ → Bool)
    (hc : ∀ u v, 0 ≤ capacity u v) (hl : ∀ u v, 0 ≤ length u v)
    (hseed : 0 < seed) (hd : 0 < delta) (hp : 0 < p)
    (hweight : weight capacity length ≤ (p : ℚ) * seed)
    (houtLip : ∀ u v, outDistance v - outDistance u ≤ length u v)
    (hinLip : ∀ u v, inDistance v - inDistance u ≤ length v u) :
    ∃ r ∈ candidates outDistance inDistance (RegionBudget.steps p) delta,
      0 < r ∧ Good capacity length outDistance inDistance seed
        (slope (RegionBudget.steps p) delta) direction r := by
  let k := RegionBudget.steps p
  let values := fun j => productVolume capacity length outDistance inDistance seed (grid k delta j)
  have hk : 0 < k := RegionBudget.steps_pos p
  have hpq : (1 : ℚ) ≤ p := by exact_mod_cast hp
  have hstart : seed ^ 2 ≤ values 0 :=
    (RegionInterval.budget capacity length outDistance inDistance seed _ hc hl hseed.le).1
  have hbudget : values k ≤ 4 * (p : ℚ) ^ 2 * seed ^ 2 :=
    RegionInterval.normalized_budget capacity length outDistance inDistance seed _ p
      hc hl hseed.le hpq hweight
  obtain ⟨j, hj, hnotDouble⟩ := FiniteRegionGrowth.exists_not_doubling values k seed p
    hseed hstart hbudget (RegionBudget.exceeds_budget p hp)
  by_contra h
  have hbad : ∀ r ∈ RegionThresholds.events outDistance inDistance
      (grid k delta j) (grid k delta (j + 1)), 0 < r →
      slope k delta * volume capacity length outDistance seed r ≤ boundary capacity outDistance r ∨
      slope k delta * volume (fun u v => capacity v u) (fun u v => length v u) inDistance seed r ≤
        boundary (fun u v => capacity v u) inDistance r := by
    intro r hr hpos
    have hmem : r ∈ candidates outDistance inDistance k delta := by
      apply List.mem_flatMap.mpr
      refine ⟨j, List.mem_range.mpr hj, ?_⟩
      exact (Finset.mem_sort (· ≤ ·)).mpr hr
    have hfail : ¬ Good capacity length outDistance inDistance seed (slope k delta) direction r := by
      intro hg
      exact h ⟨r, hmem, hpos, hg⟩
    cases hdir : direction r with
    | false =>
      right
      exact le_of_not_ge (by simpa [Good, selectedBoundary, selectedVolume, hdir] using hfail)
    | true =>
      left
      exact le_of_not_ge (by simpa [Good, selectedBoundary, selectedVolume, hdir] using hfail)
  have hdoubled := RegionCell.doubles capacity length outDistance inDistance seed
    (grid k delta j) (grid k delta (j + 1)) (slope k delta) hc hl hseed.le
    (grid_nonneg k delta j hd.le) (grid_mono k delta j hd.le)
    (by unfold slope; positivity) houtLip hinLip hbad
    (by rw [grid_width k delta j hk hd])
  exact (not_le_of_gt hnotDouble) hdoubled

/-- The concrete list search returns a successful positive threshold. -/
theorem search_correct {n : ℕ} (capacity length : Matrix n)
    (outDistance inDistance : Fin n → ℚ) (seed delta : ℚ) (p : ℕ)
    (direction : ℚ → Bool)
    (hc : ∀ u v, 0 ≤ capacity u v) (hl : ∀ u v, 0 ≤ length u v)
    (hseed : 0 < seed) (hd : 0 < delta) (hp : 0 < p)
    (hweight : weight capacity length ≤ (p : ℚ) * seed)
    (houtLip : ∀ u v, outDistance v - outDistance u ≤ length u v)
    (hinLip : ∀ u v, inDistance v - inDistance u ≤ length v u) :
    ∃ r, search capacity length outDistance inDistance seed delta p direction = some r ∧
      r ∈ candidates outDistance inDistance (RegionBudget.steps p) delta ∧
      0 < r ∧ Good capacity length outDistance inDistance seed
        (slope (RegionBudget.steps p) delta) direction r := by
  obtain ⟨r, hr, hpositive, hgood⟩ := exists_good capacity length outDistance inDistance
    seed delta p direction hc hl hseed hd hp hweight houtLip hinLip
  cases hs : search capacity length outDistance inDistance seed delta p direction with
  | none =>
    unfold search at hs
    have hnone := List.find?_eq_none.mp hs r hr
    simp only [decide_eq_true_eq] at hnone
    exact False.elim (hnone ⟨hpositive, hgood⟩)
  | some result =>
    refine ⟨result, rfl, List.mem_of_find?_eq_some hs, ?_⟩
    have hfound := List.find?_some hs
    simpa only [decide_eq_true_eq] using hfound

/-- A returned threshold respects the radius budget as well as positivity. -/
theorem search_radius {n : ℕ} (capacity length : Matrix n)
    (outDistance inDistance : Fin n → ℚ) (seed delta : ℚ) (p : ℕ)
    (direction : ℚ → Bool) (r : ℚ) (hd : 0 ≤ delta)
    (hs : search capacity length outDistance inDistance seed delta p direction = some r) :
    0 < r ∧ r ≤ delta := by
  have hfound : 0 < r ∧ Good capacity length outDistance inDistance seed
      (slope (RegionBudget.steps p) delta) direction r := by
    simpa only [decide_eq_true_eq] using List.find?_some hs
  exact ⟨hfound.1, (candidates_bound outDistance inDistance (RegionBudget.steps p) delta r
    (RegionBudget.steps_pos p) hd (List.mem_of_find?_eq_some hs)).2⟩

end Lax455465Proofs.RegionSearch
