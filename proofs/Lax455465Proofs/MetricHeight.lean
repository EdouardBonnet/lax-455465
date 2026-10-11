import Lax455465Proofs.RationalDistances
import Lax455465Proofs.LpInputSize

namespace Lax455465Proofs.MetricHeight

open scoped BigOperators
open RationalDistances DirectedFlowLP

/-- Every distance remains on the denominator lattice of the input matrix. -/
def denominator {n : ℕ} (d : Distance n) : ℕ := ∏ e : Edge n, (d e.1 e.2).den

theorem denominator_pos {n : ℕ} (d : Distance n) : 0 < denominator d := by
  apply Finset.prod_pos
  intro e he
  exact Rat.den_pos _

theorem denominator_dvd {n : ℕ} (d : Distance n) (u v : Fin n) :
    (d u v).den ∣ denominator d := Finset.dvd_prod_of_mem _ (Finset.mem_univ (u,v))

theorem step_denominator {n : ℕ} (d : Distance n) (p : Fin n) (D : ℕ)
    (h : ∀ u v, (d u v).den ∣ D) : ∀ u v, (step d p u v).den ∣ D := by
  intro u v
  by_cases hv : d u v ≤ d u p+d p v
  · rw [step,min_eq_left hv]
    exact h u v
  · rw [step,min_eq_right (le_of_not_ge hv)]
    exact (Rat.add_den_dvd_lcm _ _).trans (Nat.lcm_dvd (h u p) (h p v))

theorem iterate_denominator {n : ℕ} (d : Distance n) (ps : List (Fin n)) (D : ℕ)
    (h : ∀ u v, (d u v).den ∣ D) : ∀ u v, (iterate d ps u v).den ∣ D := by
  induction ps generalizing d with
  | nil => exact h
  | cons p ps ih => exact ih (step d p) (step_denominator d p D h)

theorem value_bound (q : ℚ) (hq : 0 ≤ q) (M : ℕ) (hnum : q.num.natAbs ≤ M) : q ≤ M := by
  have hn : (q.num.natAbs : ℤ) = q.num := Int.natAbs_of_nonneg (Rat.num_nonneg.mpr hq)
  have hnQ : (q.num.natAbs : ℚ) = (q.num : ℚ) := by
    simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z : ℚ)) hn
  have hd : (1 : ℚ) ≤ q.den := by exact_mod_cast (Rat.den_pos q)
  rw [←q.num_div_den,←hnQ]
  exact (div_le_self (by positivity) hd).trans (by exact_mod_cast hnum)

theorem height_of_denominator (q : ℚ) (hq : 0 ≤ q) (M D : ℕ)
    (hM : 1 ≤ M) (hD : 0 < D) (hden : q.den ∣ D) (hval : q ≤ M) :
    LpInputSize.Height (M*D) q := by
  have hd : q.den ≤ D := Nat.le_of_dvd hD hden
  have hn : (q.num.natAbs : ℤ) = q.num := Int.natAbs_of_nonneg (Rat.num_nonneg.mpr hq)
  have hnQ : (q.num.natAbs : ℚ) = (q.num : ℚ) := by
    simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z : ℚ)) hn
  have hdenQ : (0 : ℚ) < q.den := by exact_mod_cast Rat.den_pos q
  have hrepr : (q.num.natAbs : ℚ) = q*(q.den : ℚ) := by
    rw [hnQ]
    exact ((eq_div_iff (ne_of_gt hdenQ)).mp q.num_div_den.symm).symm
  have hbound : (q.num.natAbs : ℚ) ≤ (M*D : ℕ) := by
    rw [hrepr,Nat.cast_mul]
    exact (mul_le_mul_of_nonneg_right hval (le_of_lt hdenQ)).trans
      (mul_le_mul_of_nonneg_left (by exact_mod_cast hd) (by positivity))
  exact ⟨by exact_mod_cast hbound,hd.trans (by nlinarith)⟩

/-- The bounds hold after every prefix of the pivot list, so they cover all
intermediate matrices as well as the final output. -/
theorem iterate_height {n : ℕ} (d : Distance n) (ps : List (Fin n)) (M : ℕ)
    (hM : 1 ≤ M) (hnonneg : Nonnegative d)
    (hnum : ∀ u v, (d u v).num.natAbs ≤ M) :
    ∀ u v, LpInputSize.Height (M*denominator d) (iterate d ps u v) := by
  intro u v
  apply height_of_denominator _ (nonnegative_iterate d ps hnonneg u v) M (denominator d) hM
    (denominator_pos d) (iterate_denominator d ps _ (denominator_dvd d) u v)
  exact (iterate_le d ps u v).trans (value_bound _ (hnonneg u v) M (hnum u v))

theorem denominator_bound {n : ℕ} (d : Distance n) (w : ℕ)
    (hden : ∀ u v, (d u v).den ≤ 2^w) : denominator d ≤ 2^(w*(n*n)) := by
  unfold denominator
  calc
    _ ≤ ∏ e : Edge n, 2^w := Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun e _ => hden e.1 e.2)
    _ = _ := by simp [Edge,Finset.prod_const,Nat.pow_mul]

/-- Common denominators avoid a spurious exponential recurrence from
bounding each min-plus operation independently. The bit height is linear
in the number of matrix entries and the initial coordinate width. -/
theorem iterate_word_height {n : ℕ} (d : Distance n) (ps : List (Fin n)) (w : ℕ)
    (hnonneg : Nonnegative d)
    (hnum : ∀ u v, (d u v).num.natAbs ≤ 2^w)
    (hden : ∀ u v, (d u v).den ≤ 2^w) :
    ∀ u v, LpInputSize.Height (2^(w*(n*n+1))) (iterate d ps u v) := by
  intro u v
  have hM : 1 ≤ 2^w := Nat.succ_le_iff.mpr (Nat.two_pow_pos w)
  apply LpInputSize.height_mono (iterate_height d ps (2^w) hM hnonneg hnum u v)
  calc
    2^w*denominator d ≤ 2^w*2^(w*(n*n)) := Nat.mul_le_mul_left _ (denominator_bound d w hden)
    _ = _ := by rw [←Nat.pow_add]; congr 1; ring

/-- The sum compared in a pivot has the same common denominator; only
its value bound doubles. Its normalized representation has linear height. -/
theorem candidate_height {n : ℕ} (d : Distance n) (ps : List (Fin n)) (M : ℕ)
    (hM : 1 ≤ M) (hnonneg : Nonnegative d)
    (hnum : ∀ u v, (d u v).num.natAbs ≤ M) (u p v : Fin n) :
    LpInputSize.Height (2*(M*denominator d))
      (iterate d ps u p+iterate d ps p v) := by
  have hd := iterate_denominator d ps (denominator d) (denominator_dvd d)
  have hn := nonnegative_iterate d ps hnonneg
  have hb : ∀ a b, iterate d ps a b ≤ (M : ℚ) := fun a b =>
    (iterate_le d ps a b).trans (value_bound _ (hnonneg a b) M (hnum a b))
  have h := height_of_denominator _ (add_nonneg (hn u p) (hn p v)) (2*M) (denominator d)
    (by omega) (denominator_pos d)
    ((Rat.add_den_dvd_lcm _ _).trans (Nat.lcm_dvd (hd u p) (hd p v)))
    (by push_cast; linarith [hb u p,hb p v])
  simpa only [Nat.mul_assoc] using h

/-- Apply the common-denominator bound to the precise lengths supplied by
an LP dual, including the explicit diagonal-zero initialization. -/
theorem dual_height {n : ℕ}
    (y : Fin (n*n+2*((n*n)*n)) → ℚ) (hy : ∀ i, 0 ≤ y i) (w : ℕ)
    (hnum : ∀ i, (y i).num.natAbs ≤ 2^w) (hden : ∀ i, (y i).den ≤ 2^w)
    (ps : List (Fin n)) :
    ∀ u v, LpInputSize.Height (2^(w*(n*n+1)))
      (iterate (zeroDiagonal (DirectedFlowDual.length y)) ps u v) := by
  apply iterate_word_height
  · apply nonnegative_zeroDiagonal
    intro u v
    exact hy _
  · intro u v
    unfold zeroDiagonal
    split_ifs
    · simp
    · exact hnum _
  · intro u v
    unfold zeroDiagonal
    split_ifs
    · simpa using Nat.succ_le_iff.mpr (Nat.two_pow_pos w)
    · exact hden _

theorem candidate_word_height {n : ℕ} (d : Distance n) (ps : List (Fin n)) (w : ℕ)
    (hnonneg : Nonnegative d)
    (hnum : ∀ u v, (d u v).num.natAbs ≤ 2^w)
    (hden : ∀ u v, (d u v).den ≤ 2^w) (u p v : Fin n) :
    LpInputSize.Height (2*2^(w*(n*n+1)))
      (iterate d ps u p+iterate d ps p v) := by
  have hM : 1 ≤ 2^w := Nat.succ_le_iff.mpr (Nat.two_pow_pos w)
  apply LpInputSize.height_mono (candidate_height d ps (2^w) hM hnonneg hnum u p v)
  apply Nat.mul_le_mul_left 2
  calc
    2^w*denominator d ≤ 2^w*2^(w*(n*n)) := Nat.mul_le_mul_left _ (denominator_bound d w hden)
    _ = _ := by rw [←Nat.pow_add]; congr 1; ring

end Lax455465Proofs.MetricHeight

