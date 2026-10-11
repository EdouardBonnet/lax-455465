import Lax455465Proofs.CutSweeps

open scoped BigOperators

namespace Lax455465Proofs.CutLayers

open Lax455465.RationalEncoding Lax455465Proofs.CutSweeps

/-- A finite threshold decomposition. Ranks record the levels of each vertex. -/
structure Layers (n k : ℕ) where
  rank : Fin n → Fin (k + 1)
  gap : Fin k → ℚ
  gap_nonneg : ∀ i, 0 ≤ gap i

/-- The cumulative potential represented by the threshold gaps. -/
def potential {n k : ℕ} (L : Layers n k) (v : Fin n) : ℚ :=
  ∑ i : Fin k, if i.val < (L.rank v).val then L.gap i else 0

/-- The low-potential shore immediately after level i. -/
def shore {n k : ℕ} (L : Layers n k) (i : Fin k) : Finset (Fin n) :=
  Finset.univ.filter fun v => (L.rank v).val ≤ i.val

/-- The potential difference telescopes over the thresholds separating two vertices. -/
theorem difference {n k : ℕ} (L : Layers n k) (u v : Fin n)
    (h : (L.rank u).val ≤ (L.rank v).val) :
    potential L v - potential L u =
      ∑ i : Fin k, if (L.rank u).val ≤ i.val ∧ i.val < (L.rank v).val
        then L.gap i else 0 := by
  rw [potential, potential, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp_all <;> omega

/-- The represented potential respects the vertex ranks. -/
theorem monotone {n k : ℕ} (L : Layers n k) (u v : Fin n)
    (h : (L.rank u).val ≤ (L.rank v).val) : potential L u ≤ potential L v := by
  have hd := difference L u v h
  have hnonneg : 0 ≤ ∑ i : Fin k,
      if (L.rank u).val ≤ i.val ∧ i.val < (L.rank v).val then L.gap i else 0 :=
    Finset.sum_nonneg (fun i _ => by split_ifs; exact L.gap_nonneg i; exact le_rfl)
  linarith

/-- Exact finite layer-cake identity; no real integration or numerical approximation. -/
theorem positive_difference {n k : ℕ} (L : Layers n k) (u v : Fin n) :
    max (potential L v - potential L u) 0 =
      ∑ i : Fin k, if u ∈ shore L i ∧ v ∉ shore L i then L.gap i else 0 := by
  simp only [shore, Finset.mem_filter, Finset.mem_univ, true_and, not_le]
  by_cases h : (L.rank u).val ≤ (L.rank v).val
  · rw [max_eq_left (sub_nonneg.mpr (monotone L u v h)), difference L u v h]
  · have hrev : (L.rank v).val ≤ (L.rank u).val := by omega
    rw [max_eq_right (sub_nonpos.mpr (monotone L v u hrev))]
    symm
    apply Finset.sum_eq_zero
    intro i _
    rw [if_neg (by omega)]

private theorem complement_filter {n : ℕ} (S : Finset (Fin n)) :
    (Finset.univ.filter fun v => v ∉ S) = Sᶜ := by
  ext v
  simp

/-- Expand separated product demand as a sum over crossing ordered pairs. -/
theorem mass_product {n : ℕ} (I : RationalInstance n) (S : Finset (Fin n)) :
    massQ I S * massQ I Sᶜ =
      ∑ u : Fin n, ∑ v : Fin n,
        if u ∈ S ∧ v ∉ S then (I.weight u : ℚ) * I.weight v else 0 := by
  simp only [massQ]
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  symm
  simp_rw [ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero]
  simp only [← Finset.sum_filter]
  simp [complement_filter]

/-- Expand a directed boundary capacity over all ordered pairs. -/
theorem capacity_expansion {n : ℕ} (I : RationalInstance n) (S : Finset (Fin n)) :
    capacityQ I S =
      ∑ u : Fin n, ∑ v : Fin n,
        if u ∈ S ∧ v ∉ S then (I.capacity u v : ℚ) else 0 := by
  simp only [capacityQ]
  symm
  simp_rw [ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero]
  simp only [← Finset.sum_filter]
  simp [complement_filter]

/-- Weighted separation is the sum of layer widths times separated cut demands. -/
theorem demand_identity {n k : ℕ} (I : RationalInstance n) (L : Layers n k) :
    (∑ u : Fin n, ∑ v : Fin n,
      (I.weight u : ℚ) * I.weight v * max (potential L v - potential L u) 0) =
      ∑ i : Fin k, L.gap i * (massQ I (shore L i) * massQ I (shore L i)ᶜ) := by
  simp_rw [positive_difference, Finset.mul_sum]
  conv_lhs =>
    arg 2
    ext u
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [mass_product, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  split_ifs <;> ring

/-- Weighted positive edge differences equal the sum of weighted cut boundaries. -/
theorem capacity_identity {n k : ℕ} (I : RationalInstance n) (L : Layers n k) :
    (∑ u : Fin n, ∑ v : Fin n,
      (I.capacity u v : ℚ) * max (potential L v - potential L u) 0) =
      ∑ i : Fin k, L.gap i * capacityQ I (shore L i) := by
  simp_rw [positive_difference, Finset.mul_sum]
  conv_lhs =>
    arg 2
    ext u
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [capacity_expansion, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  split_ifs <;> ring

end Lax455465Proofs.CutLayers
