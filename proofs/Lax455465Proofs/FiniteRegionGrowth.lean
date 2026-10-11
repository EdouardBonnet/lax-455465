import Mathlib.Tactic

open scoped BigOperators

namespace Lax455465Proofs.FiniteRegionGrowth

/-- Growth of one monotone volume implies growth of the product. The boundary
comparison uses the endpoint volume, as the actual threshold search does. -/
theorem product_gain_left (a b A B width beta cut : ℚ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hA : a ≤ A) (hB : b ≤ B)
    (hw : 0 ≤ width) (hbeta : 0 ≤ beta)
    (hcut : beta * A ≤ cut) (hgain : width * cut ≤ A - a) :
    width * beta * (a * b) ≤ A * B - a * b := by
  have hfirst : width * beta * a ≤ A - a := by
    calc
      width * beta * a ≤ width * beta * A :=
        mul_le_mul_of_nonneg_left hA (mul_nonneg hw hbeta)
      _ = width * (beta * A) := by ring
      _ ≤ width * cut := mul_le_mul_of_nonneg_left hcut hw
      _ ≤ A - a := hgain
  have hsecond := mul_le_mul_of_nonneg_right hfirst hb
  have hthird := mul_le_mul_of_nonneg_left hB (ha.trans hA)
  nlinarith

/-- Either orientation can supply the growth; the other remains monotone. -/
theorem product_gain_right (a b A B width beta cut : ℚ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hA : a ≤ A) (hB : b ≤ B)
    (hw : 0 ≤ width) (hbeta : 0 ≤ beta)
    (hcut : beta * B ≤ cut) (hgain : width * cut ≤ B - b) :
    width * beta * (a * b) ≤ A * B - a * b := by
  simpa only [mul_comm b a, mul_comm B A] using
    product_gain_left b a B A width beta cut hb ha hB hA hw hbeta hcut hgain

/-- Summing the event-free intervals in one grid cell gives a growth bound
in terms of the cell's initial product. No numerical integration is needed. -/
theorem subdivided_gain (product radius : ℕ → ℚ) (beta : ℚ) (k : ℕ)
    (hbeta : 0 ≤ beta)
    (hwidth : ∀ i < k, radius i ≤ radius (i + 1))
    (hbase : ∀ i < k, product 0 ≤ product i)
    (hgain : ∀ i < k,
      (radius (i + 1) - radius i) * beta * product i ≤
        product (i + 1) - product i) :
    (radius k - radius 0) * beta * product 0 ≤ product k - product 0 := by
  have hsum : ∑ i ∈ Finset.range k,
      (radius (i + 1) - radius i) * beta * product 0 ≤
      ∑ i ∈ Finset.range k, (product (i + 1) - product i) := by
    apply Finset.sum_le_sum
    intro i hi
    have hik := Finset.mem_range.mp hi
    exact (mul_le_mul_of_nonneg_left (hbase i hik)
      (mul_nonneg (sub_nonneg.mpr (hwidth i hik)) hbeta)).trans (hgain i hik)
  simpa only [← Finset.sum_mul, Finset.sum_range_sub] using hsum

/-- A grid cell doubles the product when its width times the slope is at
least one and no tested threshold meets the boundary bound. -/
theorem doubled_cell (product radius : ℕ → ℚ) (beta : ℚ) (k : ℕ)
    (hbeta : 0 ≤ beta) (hproduct : 0 ≤ product 0)
    (hwidth : ∀ i < k, radius i ≤ radius (i + 1))
    (hbase : ∀ i < k, product 0 ≤ product i)
    (hgain : ∀ i < k,
      (radius (i + 1) - radius i) * beta * product i ≤
        product (i + 1) - product i)
    (hcell : 1 ≤ (radius k - radius 0) * beta) :
    2 * product 0 ≤ product k := by
  have hgrowth := subdivided_gain product radius beta k hbeta hwidth hbase hgain
  have hminimum := mul_le_mul_of_nonneg_right hcell hproduct
  nlinarith

/-- The finite search cannot fail on every grid cell once the exponential
lower bound exceeds the available product-volume budget. -/
theorem exists_not_doubling (product : ℕ → ℚ) (k : ℕ) (seed p : ℚ)
    (hseed : 0 < seed) (hstart : seed ^ 2 ≤ product 0)
    (hbudget : product k ≤ 4 * p ^ 2 * seed ^ 2)
    (hsteps : 4 * p ^ 2 < (2 : ℚ) ^ k) :
    ∃ j < k, product (j + 1) < 2 * product j := by
  by_contra h
  have hdouble : ∀ j < k, 2 * product j ≤ product (j + 1) := by
    intro j hj
    exact le_of_not_gt (fun hlt => h ⟨j, hj, hlt⟩)
  have hgrowth : ∀ j : ℕ, j ≤ k → (2 : ℚ) ^ j * product 0 ≤ product j := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      calc
        (2 : ℚ) ^ (j + 1) * product 0 = 2 * ((2 : ℚ) ^ j * product 0) := by
          rw [pow_succ]
          ring
        _ ≤ 2 * product j := mul_le_mul_of_nonneg_left (ih (by omega)) (by norm_num)
        _ ≤ product (j + 1) := hdouble j (by omega)
  have hpow := hgrowth k le_rfl
  have hstart' := mul_le_mul_of_nonneg_left hstart (pow_nonneg (show (0 : ℚ) ≤ 2 by norm_num) k)
  have hexcess := mul_lt_mul_of_pos_right hsteps (sq_pos_of_pos hseed)
  linarith

end Lax455465Proofs.FiniteRegionGrowth
