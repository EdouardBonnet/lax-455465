import Lax455465Proofs.CutLayers

open scoped BigOperators

namespace Lax455465Proofs.ThresholdRounding

open Lax455465.RationalEncoding Lax455465Proofs.CutSweeps Lax455465Proofs.CutLayers

/-- Exact product-weighted separation supplied by a threshold potential. -/
def separation {n k : ℕ} (I : RationalInstance n) (L : Layers n k) : ℚ :=
  ∑ u : Fin n, ∑ v : Fin n,
    (I.weight u : ℚ) * I.weight v * max (potential L v - potential L u) 0

/-- Capacity-weighted positive potential differences. -/
def edgeCost {n k : ℕ} (I : RationalInstance n) (L : Layers n k) : ℚ :=
  ∑ u : Fin n, ∑ v : Fin n,
    (I.capacity u v : ℚ) * max (potential L v - potential L u) 0

/-- There are exactly k layer shores to compare, with rational cut arithmetic. -/
def layerCandidates {n k : ℕ} (L : Layers n k) : List (Finset (Fin n)) :=
  List.ofFn (shore L)

def round {n k : ℕ} (I : RationalInstance n) (L : Layers n k) :
    Option (Finset (Fin n)) := choose I (layerCandidates L)

private theorem admissible_layer {n k : ℕ} (I : RationalInstance n) (L : Layers n k)
    (hsep : 0 < separation I L) : ∃ i : Fin k, admissibleQ I (shore L i) := by
  by_contra h
  have hzero : ∀ i : Fin k, massQ I (shore L i) * massQ I (shore L i)ᶜ = 0 := by
    intro i
    apply demand_zero_of_not_admissible
    exact fun hi => h ⟨i, hi⟩
  have hid := demand_identity I L
  change separation I L = _ at hid
  simp only [hzero, mul_zero, Finset.sum_const_zero] at hid
  exact (ne_of_gt hsep) hid

/-- The finite deterministic choice succeeds and bounds cut ratio by cost/separation. -/
theorem round_spec {n k : ℕ} (I : RationalInstance n) (L : Layers n k)
    (hsep : 0 < separation I L) :
    ∃ S, round I L = some S ∧ admissibleQ I S ∧
      ratioQ I S ≤ edgeCost I L / separation I L := by
  obtain ⟨i, hi⟩ := admissible_layer I L hsep
  have himem : shore L i ∈ layerCandidates L := List.mem_ofFn.mpr ⟨i, rfl⟩
  obtain ⟨S, hS⟩ := choose_exists I (layerCandidates L) ⟨_, himem, hi⟩
  have hvalid := (choose_sound I _ _ hS).2
  refine ⟨S, hS, hvalid, (le_div_iff₀ hsep).mpr ?_⟩
  have hcut : ∀ j : Fin k,
      ratioQ I S * (massQ I (shore L j) * massQ I (shore L j)ᶜ) ≤
        capacityQ I (shore L j) := by
    intro j
    by_cases hj : admissibleQ I (shore L j)
    · have hjmem : shore L j ∈ layerCandidates L := List.mem_ofFn.mpr ⟨j, rfl⟩
      have hmin := choose_minimal I _ S (shore L j) hS hjmem hj
      unfold ratioQ at hmin
      exact (le_div_iff₀ ((admissibleQ_iff_product_pos I _).mp hj)).mp hmin
    · rw [demand_zero_of_not_admissible I _ hj, mul_zero]
      exact capacityQ_nonneg I _
  change ratioQ I S * (∑ u, ∑ v, _) ≤ ∑ u, ∑ v, _
  rw [demand_identity, capacity_identity, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  have hbound := mul_le_mul_of_nonneg_left (hcut j) (L.gap_nonneg j)
  nlinarith

/-- A directed Lipschitz potential bounds the sweep cost by the dual length cost. -/
theorem edgeCost_le {n k : ℕ} (I : RationalInstance n) (L : Layers n k)
    (length : Fin n → Fin n → ℚ)
    (hnonneg : ∀ u v, 0 ≤ length u v)
    (hlip : ∀ u v, potential L v - potential L u ≤ length u v) :
    edgeCost I L ≤ ∑ u, ∑ v, (I.capacity u v : ℚ) * length u v := by
  apply Finset.sum_le_sum
  intro u _
  apply Finset.sum_le_sum
  intro v _
  exact mul_le_mul_of_nonneg_left (max_le (hlip u v) (hnonneg u v))
    (NNRat.coe_nonneg (I.capacity u v))

end Lax455465Proofs.ThresholdRounding
