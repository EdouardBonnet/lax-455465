import Lax455465Proofs.RegionCharging

open scoped BigOperators

namespace Lax455465Proofs.RegionOrdering

open RegionVolume

/-- Inward regions are placed first in creation order, unremoved vertices
in the middle, and outward regions last in reverse creation order. -/
def position (k : ℕ) (orientation : ℕ → Bool) (j : ℕ) : ℕ :=
  if j = k then k else if orientation j then 2 * k - j else j

def lateCut {n k : ℕ} (index : Fin n → Fin (k + 1)) (orientation : ℕ → Bool)
    (threshold : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun v => threshold < position k orientation (index v).val

/-- Capacity charged when the earliest endpoint is removed in its chosen orientation. -/
def edgeCharge {n k : ℕ} (capacity : Matrix n) (index : Fin n → Fin (k + 1))
    (orientation : ℕ → Bool) (j : Fin k) (u v : Fin n) : ℚ :=
  if orientation j.val then
    if (index u).val = j.val ∧ j.val < (index v).val then capacity u v else 0
  else if (index v).val = j.val ∧ j.val < (index u).val then capacity u v else 0

def chargedBoundary {n k : ℕ} (capacity : Matrix n) (index : Fin n → Fin (k + 1))
    (orientation : ℕ → Bool) (j : Fin k) : ℚ := ∑ u, ∑ v, edgeCharge capacity index orientation j u v

def cutCapacity {n : ℕ} (capacity : Matrix n) (S : Finset (Fin n)) : ℚ :=
  ∑ u, ∑ v, if u ∈ S ∧ v ∉ S then capacity u v else 0

private theorem earlier_outward (k : ℕ) (orientation : ℕ → Bool) (i j : ℕ)
    (hij : i < j) (hj : j ≤ k) (hi : orientation i = true) :
    position k orientation j < position k orientation i := by
  unfold position
  split_ifs <;> (try simp_all) <;> omega

private theorem earlier_inward (k : ℕ) (orientation : ℕ → Bool) (i j : ℕ)
    (hij : i < j) (hj : j ≤ k) (hi : orientation i = false) :
    position k orientation i < position k orientation j := by
  unfold position
  split_ifs <;> (try simp_all) <;> omega

/-- Every arc from a later position to an earlier one is charged at its
first removed endpoint. -/
theorem backward_arc_charged {n k : ℕ} (capacity : Matrix n)
    (index : Fin n → Fin (k + 1)) (orientation : ℕ → Bool) (u v : Fin n)
    (hback : position k orientation (index v).val < position k orientation (index u).val) :
    ∃ j : Fin k, edgeCharge capacity index orientation j u v = capacity u v := by
  have hneq : (index u).val ≠ (index v).val := by
    intro heq
    rw [heq] at hback
    exact (lt_irrefl _) hback
  rcases Nat.lt_or_gt_of_ne hneq with huv | hvu
  · have hik : (index u).val < k := by have h := (index v).isLt; omega
    have hout : orientation (index u).val = true := by
      cases heq : orientation (index u).val with
      | true => rfl
      | false =>
        have hforward := earlier_inward k orientation _ _ huv (by have h := (index v).isLt; omega) heq
        omega
    refine ⟨⟨(index u).val, hik⟩, ?_⟩
    simp only [edgeCharge, hout, ↓reduceIte, huv, and_self]
  · have hik : (index v).val < k := by have h := (index u).isLt; omega
    have hin : orientation (index v).val = false := by
      cases heq : orientation (index v).val with
      | false => rfl
      | true =>
        have hforward := earlier_outward k orientation _ _ hvu (by have h := (index u).isLt; omega) heq
        omega
    refine ⟨⟨(index v).val, hik⟩, ?_⟩
    simp only [edgeCharge, hin, Bool.false_eq_true, ↓reduceIte, hvu, and_self]

theorem edgeCharge_nonnegative {n k : ℕ} (capacity : Matrix n)
    (index : Fin n → Fin (k + 1)) (orientation : ℕ → Bool) (j : Fin k) (u v : Fin n)
    (hc : ∀ u v, 0 ≤ capacity u v) : 0 ≤ edgeCharge capacity index orientation j u v := by
  unfold edgeCharge
  split_ifs <;> first | exact hc u v | exact le_rfl

/-- Every cut between ordered regions is controlled by the sum of their
chosen removal boundaries. -/
theorem late_cut_bound {n k : ℕ} (capacity : Matrix n) (index : Fin n → Fin (k + 1))
    (orientation : ℕ → Bool) (threshold : ℕ) (hc : ∀ u v, 0 ≤ capacity u v) :
    cutCapacity capacity (lateCut index orientation threshold) ≤
      ∑ j : Fin k, chargedBoundary capacity index orientation j := by
  have hpoint : ∀ u v : Fin n,
      (if u ∈ lateCut index orientation threshold ∧ v ∉ lateCut index orientation threshold
        then capacity u v else 0) ≤ ∑ j : Fin k, edgeCharge capacity index orientation j u v := by
    intro u v
    split_ifs with hcross
    · have hu : threshold < position k orientation (index u).val := (Finset.mem_filter.mp hcross.1).2
      have hv : position k orientation (index v).val ≤ threshold := by
        simpa only [lateCut, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] using hcross.2
      obtain ⟨j, hj⟩ := backward_arc_charged capacity index orientation u v (lt_of_le_of_lt hv hu)
      rw [← hj]
      exact Finset.single_le_sum (fun i _ => edgeCharge_nonnegative capacity index orientation i u v hc)
        (Finset.mem_univ j)
    · exact Finset.sum_nonneg fun j _ => edgeCharge_nonnegative capacity index orientation j u v hc
  unfold cutCapacity chargedBoundary
  have hsum : (∑ u, ∑ v, if u ∈ lateCut index orientation threshold ∧ v ∉ lateCut index orientation threshold
      then capacity u v else 0) ≤ ∑ u, ∑ v, ∑ j : Fin k, edgeCharge capacity index orientation j u v :=
    Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => hpoint u v
  conv_rhs at hsum =>
    arg 2
    ext u
    rw [Finset.sum_comm]
  conv_rhs at hsum => rw [Finset.sum_comm]
  exact hsum

end Lax455465Proofs.RegionOrdering
