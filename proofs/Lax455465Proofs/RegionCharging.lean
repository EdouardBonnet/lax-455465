import Lax455465Proofs.RegionSearch

open scoped BigOperators

namespace Lax455465Proofs.RegionCharging

open RegionVolume

/-- Arcs incident with the removed region are disabled in both directions. -/
def erase {n : ℕ} (capacity : Matrix n) (S : Finset (Fin n)) : Matrix n :=
  fun u v => if u ∈ S ∨ v ∈ S then 0 else capacity u v

/-- Strict rational ball used by the event-threshold search. -/
def ball {n : ℕ} (distance : Fin n → ℚ) (r : ℚ) : Finset (Fin n) :=
  Finset.univ.filter fun v => distance v < r

def chosenBall {n : ℕ} (outDistance inDistance : Fin n → ℚ)
    (direction : ℚ → Bool) (r : ℚ) : Finset (Fin n) :=
  if direction r then ball outDistance r else ball inDistance r

theorem erase_nonnegative {n : ℕ} (capacity : Matrix n) (S : Finset (Fin n))
    (hc : ∀ u v, 0 ≤ capacity u v) : ∀ u v, 0 ≤ erase capacity S u v := by
  intro u v
  unfold erase
  split_ifs
  · exact le_rfl
  · exact hc u v

theorem erase_le {n : ℕ} (capacity : Matrix n) (S : Finset (Fin n))
    (hc : ∀ u v, 0 ≤ capacity u v) : ∀ u v, erase capacity S u v ≤ capacity u v := by
  intro u v
  unfold erase
  split_ifs
  · exact hc u v
  · exact le_rfl

theorem weight_nonnegative {n : ℕ} (capacity length : Matrix n)
    (hc : ∀ u v, 0 ≤ capacity u v) (hl : ∀ u v, 0 ≤ length u v) :
    0 ≤ weight capacity length :=
  Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun v _ => mul_nonneg (hc u v) (hl u v)

/-- Exact decrease in residual length cost. -/
theorem weight_drop {n : ℕ} (capacity length : Matrix n) (S : Finset (Fin n)) :
    weight capacity length - weight (erase capacity S) length =
      ∑ u, ∑ v, if u ∈ S ∨ v ∈ S then capacity u v * length u v else 0 := by
  unfold weight
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro u _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro v _
  unfold erase
  split_ifs <;> ring

private theorem portion_outside (length base radius : ℚ)
    (hl : 0 ≤ length) (h : radius ≤ base) : edgePortion length base radius = 0 := by
  unfold edgePortion
  rw [max_eq_right (sub_nonpos.mpr h), min_eq_right hl]

/-- Every non-seed volume contribution is charged to an arc removed now. -/
theorem volume_bound {n : ℕ} (capacity length : Matrix n) (distance : Fin n → ℚ)
    (seed r : ℚ) (hc : ∀ u v, 0 ≤ capacity u v) (hl : ∀ u v, 0 ≤ length u v) :
    volume capacity length distance seed r ≤
      seed + (weight capacity length - weight (erase capacity (ball distance r)) length) := by
  rw [weight_drop]
  unfold volume
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro u _
  apply Finset.sum_le_sum
  intro v _
  by_cases hu : u ∈ ball distance r
  · rw [if_pos (Or.inl hu)]
    exact mul_le_mul_of_nonneg_left (edgePortion_le _ _ _) (hc u v)
  · have hout : r ≤ distance u := by simpa [ball, not_lt] using hu
    rw [portion_outside _ _ _ (hl u v) hout, mul_zero]
    split_ifs
    · exact mul_nonneg (hc u v) (hl u v)
    · exact le_rfl

theorem weight_transpose {n : ℕ} (capacity length : Matrix n) :
    weight (fun u v => capacity v u) (fun u v => length v u) = weight capacity length := by
  unfold weight
  rw [Finset.sum_comm]

private theorem erase_transpose {n : ℕ} (capacity : Matrix n) (S : Finset (Fin n)) :
    erase (fun u v => capacity v u) S = fun u v => erase capacity S v u := by
  funext u v
  simp only [erase, or_comm]

/-- Either selected orientation has the same residual-cost accounting. -/
theorem selected_volume_bound {n : ℕ} (capacity length : Matrix n)
    (outDistance inDistance : Fin n → ℚ) (seed r : ℚ) (direction : ℚ → Bool)
    (hc : ∀ u v, 0 ≤ capacity u v) (hl : ∀ u v, 0 ≤ length u v) :
    RegionSearch.selectedVolume capacity length outDistance inDistance seed direction r ≤
      seed + (weight capacity length -
        weight (erase capacity (chosenBall outDistance inDistance direction r)) length) := by
  cases hdir : direction r with
  | true =>
    simpa only [RegionSearch.selectedVolume, chosenBall, hdir, Bool.true_eq, ↓reduceIte] using
      volume_bound capacity length outDistance seed r hc hl
  | false =>
    have h := volume_bound (fun u v => capacity v u) (fun u v => length v u)
      inDistance seed r (fun u v => hc v u) (fun u v => hl v u)
    rw [erase_transpose, weight_transpose capacity length,
      weight_transpose (erase capacity (ball inDistance r)) length] at h
    simpa only [RegionSearch.selectedVolume, chosenBall, hdir, Bool.false_eq_true, ↓reduceIte] using h

/-- Boundary charges telescope through the successive residual length costs. -/
theorem total_boundary_bound (cost boundary volume : ℕ → ℚ) (k : ℕ) (seed beta : ℚ)
    (hbeta : 0 ≤ beta) (hfinal : 0 ≤ cost k)
    (hvolume : ∀ j < k, volume j ≤ seed + (cost j - cost (j + 1)))
    (hboundary : ∀ j < k, boundary j ≤ beta * volume j) :
    (∑ j ∈ Finset.range k, boundary j) ≤ beta * ((k : ℚ) * seed + cost 0) := by
  have hsum : (∑ j ∈ Finset.range k, boundary j) ≤
      ∑ j ∈ Finset.range k, beta * (seed + (cost j - cost (j + 1))) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hboundary j (Finset.mem_range.mp hj)).trans
      (mul_le_mul_of_nonneg_left (hvolume j (Finset.mem_range.mp hj)) hbeta)
  have htel : (∑ j ∈ Finset.range k, (cost j - cost (j + 1))) = cost 0 - cost k := by
    calc
      (∑ j ∈ Finset.range k, (cost j - cost (j + 1))) =
          -(∑ j ∈ Finset.range k, (cost (j + 1) - cost j)) := by
        rw [← Finset.sum_neg_distrib]
        simp only [neg_sub]
      _ = cost 0 - cost k := by rw [Finset.sum_range_sub]; ring
  simp_rw [mul_add] at hsum
  rw [Finset.sum_add_distrib] at hsum
  simp_rw [← Finset.mul_sum] at hsum
  rw [htel] at hsum
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  nlinarith

/-- Seed W/p and at most p removals give total boundary at most 2 beta W. -/
theorem total_boundary_normalized (cost boundary volume : ℕ → ℚ) (k p : ℕ) (beta : ℚ)
    (hp : 0 < p) (hk : k ≤ p) (hbeta : 0 ≤ beta)
    (hstart : 0 ≤ cost 0) (hfinal : 0 ≤ cost k)
    (hvolume : ∀ j < k, volume j ≤ cost 0 / p + (cost j - cost (j + 1)))
    (hboundary : ∀ j < k, boundary j ≤ beta * volume j) :
    (∑ j ∈ Finset.range k, boundary j) ≤ 2 * beta * cost 0 := by
  have h := total_boundary_bound cost boundary volume k (cost 0 / p) beta hbeta hfinal hvolume hboundary
  have hpq : (0 : ℚ) < p := by exact_mod_cast hp
  have hkq : (k : ℚ) ≤ p := by exact_mod_cast hk
  have hseed : 0 ≤ cost 0 / p := div_nonneg hstart hpq.le
  have hks := mul_le_mul_of_nonneg_right hkq hseed
  have hid : (p : ℚ) * (cost 0 / p) = cost 0 := by field_simp [ne_of_gt hpq]
  rw [hid] at hks
  have hmul := mul_le_mul_of_nonneg_left hks hbeta
  nlinarith

end Lax455465Proofs.RegionCharging
