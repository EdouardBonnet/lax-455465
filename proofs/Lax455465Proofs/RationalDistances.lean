import Lax455465Proofs.DirectedFlowDual

/-! Exact min-plus shortest distances. The algorithm has n pivots, each
updating n² rational coordinates, and does not enumerate paths. -/

open scoped BigOperators

namespace Lax455465Proofs.RationalDistances

abbrev Distance (n : ℕ) := Fin n → Fin n → ℚ

def Nonnegative {n : ℕ} (d : Distance n) : Prop := ∀ u v, 0 ≤ d u v

def ClosedAt {n : ℕ} (d : Distance n) (p : Fin n) : Prop :=
  ∀ u v, d u v ≤ d u p + d p v

/-- One exact Floyd–Warshall pivot. -/
def step {n : ℕ} (d : Distance n) (p : Fin n) : Distance n :=
  fun u v => min (d u v) (d u p + d p v)

/-- Process a fixed list of pivots in order. -/
def iterate {n : ℕ} (d : Distance n) : List (Fin n) → Distance n
  | [] => d
  | p :: rest => iterate (step d p) rest

def solve {n : ℕ} (d : Distance n) : Distance n := iterate d (List.finRange n)

theorem step_le {n : ℕ} (d : Distance n) (p u v : Fin n) : step d p u v ≤ d u v :=
  min_le_left _ _

theorem step_via {n : ℕ} (d : Distance n) (p u v : Fin n) :
    step d p u v ≤ d u p + d p v := min_le_right _ _

theorem nonnegative_step {n : ℕ} (d : Distance n) (p : Fin n) (h : Nonnegative d) :
    Nonnegative (step d p) := by
  intro u v
  exact le_min (h u v) (add_nonneg (h u p) (h p v))

/-- A processed pivot remains closed after any later pivot. -/
theorem closed_step {n : ℕ} (d : Distance n) (p q : Fin n)
    (hnonneg : Nonnegative d) (hclosed : ClosedAt d q) : ClosedAt (step d p) q := by
  intro u v
  by_cases hu : d u q ≤ d u p + d p q
  · have hlu : step d p u q = d u q := min_eq_left hu
    rw [hlu]
    by_cases hv : d q v ≤ d q p + d p v
    · rw [show step d p q v = d q v from min_eq_left hv]
      exact (step_le d p u v).trans (hclosed u v)
    · rw [show step d p q v = d q p + d p v from min_eq_right (le_of_not_ge hv)]
      have h := step_via d p u v
      have hq := hclosed u p
      linarith
  · have hlu : step d p u q = d u p + d p q := min_eq_right (le_of_not_ge hu)
    rw [hlu]
    by_cases hv : d q v ≤ d q p + d p v
    · rw [show step d p q v = d q v from min_eq_left hv]
      have h := step_via d p u v
      have hq := hclosed p v
      linarith
    · rw [show step d p q v = d q p + d p v from min_eq_right (le_of_not_ge hv)]
      have h := step_via d p u v
      have hpq := hnonneg p q
      have hqp := hnonneg q p
      linarith

/-- The newly processed pivot is closed too. -/
theorem closed_pivot {n : ℕ} (d : Distance n) (p : Fin n) (h : Nonnegative d) :
    ClosedAt (step d p) p := by
  intro u v
  have hu : step d p u p = d u p := min_eq_left (by linarith [h p p])
  have hv : step d p p v = d p v := min_eq_left (by linarith [h p p])
  rw [hu, hv]
  exact step_via d p u v

theorem nonnegative_iterate {n : ℕ} (d : Distance n) (pivots : List (Fin n))
    (h : Nonnegative d) : Nonnegative (iterate d pivots) := by
  induction pivots generalizing d with
  | nil => exact h
  | cons p rest ih => exact ih (step d p) (nonnegative_step d p h)

theorem iterate_le {n : ℕ} (d : Distance n) (pivots : List (Fin n)) (u v : Fin n) :
    iterate d pivots u v ≤ d u v := by
  induction pivots generalizing d with
  | nil => exact le_rfl
  | cons p rest ih => exact (ih (step d p)).trans (step_le d p u v)

theorem closed_iterate {n : ℕ} (d : Distance n) (pivots : List (Fin n)) (q : Fin n)
    (hnonneg : Nonnegative d) (hclosed : ClosedAt d q) : ClosedAt (iterate d pivots) q := by
  induction pivots generalizing d with
  | nil => exact hclosed
  | cons p rest ih =>
    exact ih (step d p) (nonnegative_step d p hnonneg) (closed_step d p q hnonneg hclosed)

/-- Every vertex used as a pivot satisfies the triangle inequality in the final matrix. -/
theorem pivots_closed {n : ℕ} (d : Distance n) (pivots : List (Fin n))
    (hnonneg : Nonnegative d) : ∀ q ∈ pivots, ClosedAt (iterate d pivots) q := by
  induction pivots generalizing d with
  | nil => simp
  | cons p rest ih =>
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact closed_iterate (step d q) rest q (nonnegative_step d q hnonneg)
        (closed_pivot d q hnonneg)
    · exact ih (step d p) (nonnegative_step d p hnonneg) q hq

/-- The output satisfies every directed triangle inequality. -/
theorem triangle {n : ℕ} (d : Distance n) (h : Nonnegative d) (u v w : Fin n) :
    solve d u w ≤ solve d u v + solve d v w :=
  pivots_closed d (List.finRange n) h v (List.mem_finRange v) u w

/-- Potential lower bounds survive a min-plus pivot. -/
theorem potential_step {n : ℕ} (d : Distance n) (p : Fin n) (a : Fin n → ℚ)
    (h : ∀ u v, a v - a u ≤ d u v) : ∀ u v, a v - a u ≤ step d p u v := by
  intro u v
  apply le_min (h u v)
  linarith [h u p, h p v]

theorem potential_iterate {n : ℕ} (d : Distance n) (pivots : List (Fin n))
    (a : Fin n → ℚ) (h : ∀ u v, a v - a u ≤ d u v) :
    ∀ u v, a v - a u ≤ iterate d pivots u v := by
  induction pivots generalizing d with
  | nil => exact h
  | cons p rest ih => exact ih (step d p) (potential_step d p a h)

/-- Diagonal arc multipliers carry no geometric information. -/
def zeroDiagonal {n : ℕ} (d : Distance n) : Distance n :=
  fun u v => if u = v then 0 else d u v

theorem nonnegative_zeroDiagonal {n : ℕ} (d : Distance n) (h : Nonnegative d) :
    Nonnegative (zeroDiagonal d) := by
  intro u v
  unfold zeroDiagonal
  split_ifs; exact le_rfl; exact h u v

theorem potential_zeroDiagonal {n : ℕ} (d : Distance n) (a : Fin n → ℚ)
    (h : ∀ u v, a v - a u ≤ d u v) :
    ∀ u v, a v - a u ≤ zeroDiagonal d u v := by
  intro u v
  unfold zeroDiagonal
  split_ifs with huv
  · subst v; simp
  · exact h u v

theorem diagonal_iterate {n : ℕ} (d : Distance n) (pivots : List (Fin n))
    (hnonneg : Nonnegative d) (hdiag : ∀ u, d u u = 0) :
    ∀ u, iterate d pivots u u = 0 := by
  induction pivots generalizing d with
  | nil => exact hdiag
  | cons p rest ih =>
    apply ih (step d p) (nonnegative_step d p hnonneg)
    intro u
    simp only [step, hdiag]
    exact min_eq_left (add_nonneg (hnonneg u p) (hnonneg p u))

/-- Exact directed distances derived from a feasible flow-LP dual. -/
def dualDistance {n : ℕ}
    (y : Fin (n * n + 2 * ((n * n) * n)) → ℚ) : Distance n :=
  solve (zeroDiagonal (Lax455465Proofs.DirectedFlowDual.length y))

/-- The computed distance matrix retains the product-weighted separation of the dual. -/
theorem dualDistance_spec {n : ℕ} (I : Lax455465.RationalEncoding.RationalInstance n)
    (y : Fin (n * n + 2 * ((n * n) * n)) → ℚ)
    (hy : Lax109476.LinearProgram.DualFeasible (Lax455465Proofs.DirectedFlowLP.program I) y) :
    Nonnegative (dualDistance y) ∧
    (∀ u, dualDistance y u u = 0) ∧
    (∀ u v w, dualDistance y u w ≤ dualDistance y u v + dualDistance y v w) ∧
    1 ≤ ∑ st : Lax455465Proofs.DirectedFlowLP.Edge n,
      (I.weight st.1 : ℚ) * I.weight st.2 * dualDistance y st.1 st.2 := by
  obtain ⟨hnonneg, hpot, hsep⟩ := Lax455465Proofs.DirectedFlowDual.dual_geometry I y hy
  have hinit := nonnegative_zeroDiagonal _ hnonneg
  refine ⟨nonnegative_iterate _ _ hinit, ?_, triangle _ hinit, hsep.trans ?_⟩
  · exact diagonal_iterate _ _ hinit (fun u => by simp [zeroDiagonal])
  · apply Finset.sum_le_sum
    intro st _
    exact mul_le_mul_of_nonneg_left
      (potential_iterate _ _ (Lax455465Proofs.DirectedFlowDual.potential y st)
        (potential_zeroDiagonal _ _ (hpot st)) st.1 st.2)
      (mul_nonneg (NNRat.coe_nonneg _) (NNRat.coe_nonneg _))

/-- The distance cost is at most the matching dual objective. -/
theorem dualDistance_cost {n : ℕ} (I : Lax455465.RationalEncoding.RationalInstance n)
    (y : Fin (n * n + 2 * ((n * n) * n)) → ℚ)
    (hy : Lax109476.LinearProgram.DualFeasible (Lax455465Proofs.DirectedFlowLP.program I) y) :
    (∑ u, ∑ v, (I.capacity u v : ℚ) * dualDistance y u v) ≤
      Lax109476.LinearProgram.dualValue (Lax455465Proofs.DirectedFlowLP.program I) y := by
  rw [Lax455465Proofs.DirectedFlowDual.objective_eq]
  apply Finset.sum_le_sum
  intro u _
  apply Finset.sum_le_sum
  intro v _
  apply mul_le_mul_of_nonneg_left _ (NNRat.coe_nonneg _)
  have h := iterate_le (zeroDiagonal (Lax455465Proofs.DirectedFlowDual.length y))
    (List.finRange n) u v
  apply h.trans
  unfold zeroDiagonal
  split_ifs
  · exact hy.1 _
  · exact le_rfl

end Lax455465Proofs.RationalDistances
