import Lax455465Proofs.RationalDistances

open scoped BigOperators

namespace Lax455465Proofs.RegionVolume

abbrev Matrix (n : ℕ) := Fin n → Fin n → ℚ

def edgePortion (length base radius : ℚ) : ℚ := min length (max (radius - base) 0)

/-- Seeded exact rational volume of an outward ball. Inward balls use the
transposed capacity/length arrays and distances towards the root. -/
def volume {n : ℕ} (capacity length : Matrix n) (distance : Fin n → ℚ)
    (seed radius : ℚ) : ℚ :=
  seed + ∑ u, ∑ v, capacity u v * edgePortion (length u v) (distance u) radius

def weight {n : ℕ} (capacity length : Matrix n) : ℚ :=
  ∑ u, ∑ v, capacity u v * length u v

/-- The strict ball is the left limit at a candidate threshold. -/
def boundary {n : ℕ} (capacity : Matrix n) (distance : Fin n → ℚ) (radius : ℚ) : ℚ :=
  ∑ u, ∑ v, if distance u < radius ∧ radius ≤ distance v then capacity u v else 0

/-- No vertex enters the ball in the interior of this interval. -/
def NoEvent {n : ℕ} (distance : Fin n → ℚ) (a b : ℚ) : Prop :=
  ∀ v, ¬ (a < distance v ∧ distance v < b)

theorem edgePortion_nonneg (length base radius : ℚ) (hl : 0 ≤ length) :
    0 ≤ edgePortion length base radius := le_min hl (le_max_right _ _)

theorem edgePortion_le (length base radius : ℚ) : edgePortion length base radius ≤ length :=
  min_le_left _ _

theorem edgePortion_monotone (length base a b : ℚ) (hab : a ≤ b) :
    edgePortion length base a ≤ edgePortion length base b := by
  exact min_le_min_left length (max_le_max_right 0 (sub_le_sub_right hab base))

theorem bounds {n : ℕ} (capacity length : Matrix n) (distance : Fin n → ℚ)
    (seed radius : ℚ) (hc : ∀ u v, 0 ≤ capacity u v) (hl : ∀ u v, 0 ≤ length u v) :
    seed ≤ volume capacity length distance seed radius ∧
    volume capacity length distance seed radius ≤ seed + weight capacity length := by
  constructor
  · unfold volume
    have h : 0 ≤ ∑ u, ∑ v,
        capacity u v * edgePortion (length u v) (distance u) radius :=
      Finset.sum_nonneg (fun u _ => Finset.sum_nonneg (fun v _ =>
        mul_nonneg (hc u v) (edgePortion_nonneg _ _ _ (hl u v))))
    linarith
  · unfold volume weight
    apply add_le_add le_rfl
    apply Finset.sum_le_sum
    intro u _
    apply Finset.sum_le_sum
    intro v _
    exact mul_le_mul_of_nonneg_left (edgePortion_le _ _ _) (hc u v)

theorem monotone {n : ℕ} (capacity length : Matrix n) (distance : Fin n → ℚ)
    (seed a b : ℚ) (hc : ∀ u v, 0 ≤ capacity u v) (hab : a ≤ b) :
    volume capacity length distance seed a ≤ volume capacity length distance seed b := by
  unfold volume
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro u _
  apply Finset.sum_le_sum
  intro v _
  exact mul_le_mul_of_nonneg_left (edgePortion_monotone _ _ _ _ hab) (hc u v)

/-- An arc crossing an event-free interval contributes its full capacity
throughout the interval. -/
private theorem crossing_gain (length tail head a b : ℚ)
    (hab : a ≤ b) (htail : tail ≤ a) (hhead : b ≤ head)
    (hlip : head - tail ≤ length) :
    edgePortion length tail b - edgePortion length tail a = b - a := by
  have hba : 0 ≤ b - tail := by linarith
  have haa : 0 ≤ a - tail := by linarith
  have hbl : b - tail ≤ length := by linarith
  have hal : a - tail ≤ length := by linarith
  simp only [edgePortion, max_eq_left hba, max_eq_left haa,
    min_eq_right hbl, min_eq_right hal]
  ring

/-- Finite volume-growth inequality used in the deterministic region-growing
proof. It replaces integration by exact rational differences at event thresholds. -/
theorem gain {n : ℕ} (capacity length : Matrix n) (distance : Fin n → ℚ)
    (seed a b : ℚ) (hc : ∀ u v, 0 ≤ capacity u v) (hab : a ≤ b)
    (hevent : NoEvent distance a b)
    (hlip : ∀ u v, distance v - distance u ≤ length u v) :
    (b - a) * boundary capacity distance b ≤
      volume capacity length distance seed b - volume capacity length distance seed a := by
  unfold volume boundary
  rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro u _
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro v _
  by_cases hcross : distance u < b ∧ b ≤ distance v
  · rw [if_pos hcross]
    have htail : distance u ≤ a := by
      by_contra h
      exact hevent u ⟨lt_of_not_ge h, hcross.1⟩
    have hgain := crossing_gain (length u v) (distance u) (distance v)
      a b hab htail hcross.2 (hlip u v)
    have heq : capacity u v * edgePortion (length u v) (distance u) b -
        capacity u v * edgePortion (length u v) (distance u) a =
        (b - a) * capacity u v := by
      rw [← mul_sub, hgain]
      ring
    exact le_of_eq heq.symm
  · rw [if_neg hcross, mul_zero]
    exact sub_nonneg.mpr (mul_le_mul_of_nonneg_left
      (edgePortion_monotone _ _ _ _ hab) (hc u v))

/-- If one ball volume grows by a fixed factor while the other is monotone,
their product grows by that factor too. -/
theorem product_grows_left (a b A B factor : ℚ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : a ≤ A) (hB : b ≤ B) (hgrowth : factor * a ≤ A) :
    factor * (a * b) ≤ A * B := by
  calc
    factor * (a * b) = (factor * a) * b := by ring
    _ ≤ A * b := mul_le_mul_of_nonneg_right hgrowth hb
    _ ≤ A * B := mul_le_mul_of_nonneg_left hB (ha.trans hA)

end Lax455465Proofs.RegionVolume
