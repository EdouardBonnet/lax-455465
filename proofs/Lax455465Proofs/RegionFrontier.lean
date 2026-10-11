import Lax455465Proofs.RegionOrdering

open scoped BigOperators

namespace Lax455465Proofs.RegionFrontier

open RegionVolume RegionOrdering

/-- Capacity remaining just before block j is removed. -/
def residual {n k : ℕ} (capacity : Matrix n) (index : Fin n → Fin (k + 1))
    (j : ℕ) : Matrix n :=
  fun u v => if j ≤ (index u).val ∧ j ≤ (index v).val then capacity u v else 0

private theorem outgoing_term {n k : ℕ} (capacity : Matrix n)
    (index : Fin n → Fin (k + 1)) (j : ℕ) (S : Finset (Fin n))
    (hS : ∀ v, j ≤ (index v).val → (v ∈ S ↔ (index v).val = j)) (u v : Fin n) :
    (if u ∈ S ∧ v ∉ S then residual capacity index j u v else 0) =
      if (index u).val = j ∧ j < (index v).val then capacity u v else 0 := by
  by_cases hu : j ≤ (index u).val
  · by_cases hv : j ≤ (index v).val
    · have hcond : ((index u).val = j ∧ ¬ (index v).val = j) ↔
          ((index u).val = j ∧ j < (index v).val) := by omega
      simp only [residual, hu, hv, and_self, ↓reduceIte, hS u hu, hS v hv, hcond]
    · have hnot : ¬ j < (index v).val := by omega
      simp [residual, hv, hnot]
  · have hnot : (index u).val ≠ j := by omega
    simp [residual, hu, hnot]

/-- Overlap with earlier removed balls has no effect: the residual
outgoing boundary is precisely the charge for the present block. -/
theorem outgoing_boundary {n k : ℕ} (capacity : Matrix n)
    (index : Fin n → Fin (k + 1)) (j : ℕ) (S : Finset (Fin n))
    (hS : ∀ v, j ≤ (index v).val → (v ∈ S ↔ (index v).val = j)) :
    cutCapacity (residual capacity index j) S =
      ∑ u, ∑ v, if (index u).val = j ∧ j < (index v).val then capacity u v else 0 := by
  unfold cutCapacity
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  exact outgoing_term capacity index j S hS u v

/-- The incoming residual boundary charges the same arcs after reversing
which endpoint lies in the removed block. -/
theorem incoming_boundary {n k : ℕ} (capacity : Matrix n)
    (index : Fin n → Fin (k + 1)) (j : ℕ) (S : Finset (Fin n))
    (hS : ∀ v, j ≤ (index v).val → (v ∈ S ↔ (index v).val = j)) :
    cutCapacity (fun u v => residual capacity index j v u) S =
      ∑ u, ∑ v, if (index v).val = j ∧ j < (index u).val then capacity u v else 0 := by
  have ht : (fun u v => residual capacity index j v u) =
      residual (fun u v => capacity v u) index j := by
    funext u v
    simp only [residual, and_comm]
  rw [ht, outgoing_boundary (fun u v => capacity v u) index j S hS, Finset.sum_comm]

/-- Boundary selected in the actual ball orientation. -/
def orientedBoundary {n : ℕ} (capacity : Matrix n) (S : Finset (Fin n)) (outward : Bool) : ℚ :=
  if outward then cutCapacity capacity S else cutCapacity (fun u v => capacity v u) S

/-- Each charged boundary agrees with the residual boundary that the
region-growth search bounded. -/
theorem charged_eq_boundary {n k : ℕ} (capacity : Matrix n)
    (index : Fin n → Fin (k + 1)) (orientation : ℕ → Bool) (j : Fin k)
    (S : Finset (Fin n))
    (hS : ∀ v, j.val ≤ (index v).val → (v ∈ S ↔ (index v).val = j.val)) :
    chargedBoundary capacity index orientation j =
      orientedBoundary (residual capacity index j.val) S (orientation j.val) := by
  cases hd : orientation j.val with
  | true =>
    simp only [chargedBoundary, edgeCharge, orientedBoundary, hd, ↓reduceIte]
    exact (outgoing_boundary capacity index j.val S hS).symm
  | false =>
    simp only [chargedBoundary, edgeCharge, orientedBoundary, hd, Bool.false_eq_true, ↓reduceIte]
    exact (incoming_boundary capacity index j.val S hS).symm

/-- The distance-event boundary and the actual strict-ball boundary agree. -/
theorem ball_boundary {n : ℕ} (capacity : Matrix n) (distance : Fin n → ℚ) (r : ℚ) :
    boundary capacity distance r = cutCapacity capacity (RegionCharging.ball distance r) := by
  unfold boundary cutCapacity RegionCharging.ball
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt]

/-- The selected search boundary is the oriented boundary of the selected ball. -/
theorem selected_boundary {n : ℕ} (capacity : Matrix n)
    (outDistance inDistance : Fin n → ℚ) (direction : ℚ → Bool) (r : ℚ) :
    RegionSearch.selectedBoundary capacity outDistance inDistance direction r =
      orientedBoundary capacity (RegionCharging.chosenBall outDistance inDistance direction r) (direction r) := by
  cases hd : direction r <;>
    simp only [RegionSearch.selectedBoundary, RegionCharging.chosenBall, orientedBoundary,
      hd, Bool.false_eq_true, ↓reduceIte, ball_boundary]

end Lax455465Proofs.RegionFrontier
