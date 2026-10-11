import Lax455465Proofs.RegionOrdering
import Lax455465Proofs.BalancedPrefix
import Lax455465Proofs.CutLayers

open scoped BigOperators

namespace Lax455465Proofs.BalancedRegionCut

open Lax455465.RationalEncoding CutSweeps RegionOrdering

def total {n : ℕ} (I : RationalInstance n) : ℚ := ∑ v, (I.weight v : ℚ)

def slotMass {n k : ℕ} (I : RationalInstance n) (index : Fin n → Fin (k + 1))
    (orientation : ℕ → Bool) (t : ℕ) : ℚ :=
  ∑ v, if position k orientation (index v).val = t then (I.weight v : ℚ) else 0

theorem position_injective (k : ℕ) (orientation : ℕ → Bool) (i j : ℕ)
    (hi : i ≤ k) (hj : j ≤ k) (heq : position k orientation i = position k orientation j) :
    i = j := by
  unfold position at heq
  split_ifs at heq <;> omega

/-- The mass of one removed region, or of the final unremoved block. -/
def regionMass {n k : ℕ} (I : RationalInstance n) (index : Fin n → Fin (k + 1))
    (j : Fin (k + 1)) : ℚ := ∑ v, if index v = j then (I.weight v : ℚ) else 0

/-- Reordering the blocks preserves the small-block condition. Empty slots
have zero mass, and each occupied slot contains exactly one block. -/
theorem slots_small {n k : ℕ} (I : RationalInstance n) (index : Fin n → Fin (k + 1))
    (orientation : ℕ → Bool) (hM : 0 < total I)
    (hsmall : ∀ j, regionMass I index j < (2 / 3 : ℚ) * total I) :
    ∀ t, slotMass I index orientation t < (2 / 3 : ℚ) * total I := by
  intro t
  by_cases hex : ∃ v, position k orientation (index v).val = t
  · obtain ⟨v, hv⟩ := hex
    have heq : slotMass I index orientation t = regionMass I index (index v) := by
      unfold slotMass regionMass
      apply Finset.sum_congr rfl
      intro u _
      have hiff : position k orientation (index u).val = t ↔ index u = index v := by
        constructor
        · intro hu
          apply Fin.ext
          exact position_injective k orientation _ _ (by have h := (index u).isLt; omega)
            (by have h := (index v).isLt; omega) (hu.trans hv.symm)
        · intro hu
          simpa only [hu] using hv
      simp only [hiff]
    rw [heq]
    exact hsmall (index v)
  · have hz : slotMass I index orientation t = 0 := by
      unfold slotMass
      apply Finset.sum_eq_zero
      intro v _
      exact if_neg (fun hv => hex ⟨v, hv⟩)
    rw [hz]
    linarith

private theorem position_bound (k : ℕ) (orientation : ℕ → Bool) (j : ℕ) (hj : j ≤ k) :
    position k orientation j < 2 * k + 1 := by
  unfold position
  split_ifs <;> omega

theorem slot_total {n k : ℕ} (I : RationalInstance n) (index : Fin n → Fin (k + 1))
    (orientation : ℕ → Bool) :
    (∑ t ∈ Finset.range (2 * k + 1), slotMass I index orientation t) = total I := by
  unfold slotMass total
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  rw [Finset.sum_ite_eq]
  rw [if_pos (Finset.mem_range.mpr (position_bound k orientation _ (by have h := (index v).isLt; omega)))]

/-- The low-position prefix is exactly the complementary shore of the cut. -/
theorem prefix_mass {n k : ℕ} (I : RationalInstance n) (index : Fin n → Fin (k + 1))
    (orientation : ℕ → Bool) (t : ℕ) :
    BalancedPrefix.prefixMass (slotMass I index orientation) t = massQ I (lateCut index orientation t)ᶜ := by
  unfold BalancedPrefix.prefixMass slotMass
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_range, Nat.lt_succ_iff]
  have hc : (lateCut index orientation t)ᶜ =
      Finset.univ.filter fun v => position k orientation (index v).val ≤ t := by
    ext v
    simp [lateCut, not_lt]
  rw [hc]
  unfold massQ
  rw [Finset.sum_filter]

theorem mass_complement {n : ℕ} (I : RationalInstance n) (S : Finset (Fin n)) :
    massQ I S + massQ I Sᶜ = total I := by
  exact Finset.sum_add_sum_compl S (fun v => (I.weight v : ℚ))

/-- Finite threshold scan and construction of its later shore. -/
def round {n k : ℕ} (I : RationalInstance n) (index : Fin n → Fin (k + 1))
    (orientation : ℕ → Bool) : Option (Finset (Fin n)) :=
  (BalancedPrefix.choose (slotMass I index orientation) (2 * k + 1) (total I)).map
    (lateCut index orientation)

/-- The actual threshold scan returns a positive-demand cut whose capacity
is bounded by the total chosen region boundaries. -/
theorem round_correct {n k : ℕ} (I : RationalInstance n) (index : Fin n → Fin (k + 1))
    (orientation : ℕ → Bool) (hM : 0 < total I)
    (hsmall : ∀ t < 2 * k + 1, slotMass I index orientation t < (2 / 3 : ℚ) * total I) :
    ∃ S, round I index orientation = some S ∧ admissibleQ I S ∧
      (5 / 36 : ℚ) * total I ^ 2 ≤ massQ I S * massQ I Sᶜ ∧
      capacityQ I S ≤ ∑ j : Fin k, chargedBoundary (fun u v => (I.capacity u v : ℚ)) index orientation j := by
  obtain ⟨t, ht, _, hlow, hhigh⟩ := BalancedPrefix.choose_correct
    (slotMass I index orientation) (2 * k + 1) (total I) hM (slot_total I index orientation) hsmall
  let S := lateCut index orientation t
  have hpref : BalancedPrefix.prefixMass (slotMass I index orientation) t = massQ I Sᶜ :=
    prefix_mass I index orientation t
  obtain ⟨hleft, hright, hdemand⟩ := BalancedPrefix.demand_bound (total I) _ hM hlow hhigh.le
  rw [hpref] at hleft hright hdemand
  have hcomplement := mass_complement I S
  have hS : total I - massQ I Sᶜ = massQ I S := by linarith
  rw [hS] at hright hdemand
  refine ⟨S, by simp only [round, ht, Option.map_some, S], ⟨hright, hleft⟩, ?_, ?_⟩
  · nlinarith [hdemand]
  · have hbound := late_cut_bound (fun u v => (I.capacity u v : ℚ)) index orientation t
      (fun u v => NNRat.coe_nonneg _)
    rw [CutLayers.capacity_expansion]
    exact hbound

/-- The small-region branch has ratio at most (288/5) K W once
its telescoped boundary charge is bounded by 8 K M² W. -/
theorem round_ratio {n k : ℕ} (I : RationalInstance n) (index : Fin n → Fin (k + 1))
    (orientation : ℕ → Bool) (K W : ℚ) (hM : 0 < total I) (hK : 0 ≤ K) (hW : 0 ≤ W)
    (hsmall : ∀ j, regionMass I index j < (2 / 3 : ℚ) * total I)
    (hcharge : (∑ j : Fin k, chargedBoundary (fun u v => (I.capacity u v : ℚ)) index orientation j) ≤
      8 * K * total I ^ 2 * W) :
    ∃ S, round I index orientation = some S ∧ admissibleQ I S ∧
      ratioQ I S ≤ (288 / 5 : ℚ) * K * W := by
  obtain ⟨S, hs, hadm, hdemand, hcap⟩ := round_correct I index orientation hM
    (fun t _ => slots_small I index orientation hM hsmall t)
  refine ⟨S, hs, hadm, ?_⟩
  unfold ratioQ
  apply (div_le_iff₀ (mul_pos hadm.1 hadm.2)).mpr
  calc
    capacityQ I S ≤ 8 * K * total I ^ 2 * W := hcap.trans hcharge
    _ = ((288 / 5 : ℚ) * K * W) * ((5 / 36 : ℚ) * total I ^ 2) := by ring
    _ ≤ ((288 / 5 : ℚ) * K * W) * (massQ I S * massQ I Sᶜ) :=
      mul_le_mul_of_nonneg_left hdemand (by positivity)

end Lax455465Proofs.BalancedRegionCut
