import Lax455465Proofs.RegionCharging

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace Lax455465Proofs.RegionSelection

open RegionCharging

/-- Rational mass of a strict ball in the current residual weights. -/
def ballMass {n : ℕ} (weights distance : Fin n → ℚ) (r : ℚ) : ℚ :=
  ∑ v ∈ ball distance r, weights v

/-- Ties select the outward ball. -/
def direction {n : ℕ} (weights outDistance inDistance : Fin n → ℚ) (r : ℚ) : Bool :=
  decide (ballMass weights outDistance r ≤ ballMass weights inDistance r)

/-- The chosen orientation has no greater residual mass than either ball. -/
theorem chosen_mass {n : ℕ} (weights outDistance inDistance : Fin n → ℚ) (r : ℚ) :
    (∑ v ∈ chosenBall outDistance inDistance (direction weights outDistance inDistance) r,
      weights v) = min (ballMass weights outDistance r) (ballMass weights inDistance r) := by
  by_cases h : ballMass weights outDistance r ≤ ballMass weights inDistance r
  · simp only [chosenBall, direction, decide_eq_true_eq, if_pos h, min_eq_left h]
    rfl
  · simp only [chosenBall, direction, decide_eq_true_eq, if_neg h, min_eq_right (le_of_not_ge h)]
    rfl

/-- Disabled vertices contribute zero mass to all later selections. -/
def eraseWeights {n : ℕ} (weights : Fin n → ℚ) (S : Finset (Fin n)) : Fin n → ℚ :=
  fun v => if v ∈ S then 0 else weights v

def support {n : ℕ} (weights : Fin n → ℚ) : Finset (Fin n) :=
  Finset.univ.filter fun v => 0 < weights v

def chooseRoot {n : ℕ} (weights : Fin n → ℚ) : Option (Fin n) :=
  (List.finRange n).find? fun v => decide (0 < weights v)

theorem root_correct {n : ℕ} (weights : Fin n → ℚ)
    (hp : 0 < (support weights).card) : ∃ root, chooseRoot weights = some root ∧ 0 < weights root := by
  obtain ⟨v, hv⟩ := Finset.card_pos.mp hp
  have hpositive : 0 < weights v := (Finset.mem_filter.mp hv).2
  cases hs : chooseRoot weights with
  | none =>
    unfold chooseRoot at hs
    have hfail := List.find?_eq_none.mp hs v (List.mem_finRange v)
    simp only [decide_eq_true_eq] at hfail
    exact False.elim (hfail hpositive)
  | some root =>
    refine ⟨root, rfl, ?_⟩
    simpa only [decide_eq_true_eq] using List.find?_some hs

theorem support_erase {n : ℕ} (weights : Fin n → ℚ) (S : Finset (Fin n)) :
    support (eraseWeights weights S) = support weights \ S := by
  ext v
  simp only [support, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and, eraseWeights]
  split_ifs <;> simp_all

/-- Removing a region containing a positive-weight root strictly decreases
 the iteration measure, even when zero-weight transit vertices remain. -/
theorem support_decreases {n : ℕ} (weights : Fin n → ℚ) (S : Finset (Fin n))
    (root : Fin n) (hroot : 0 < weights root) (hmem : root ∈ S) :
    (support (eraseWeights weights S)).card < (support weights).card := by
  rw [support_erase]
  apply Finset.card_lt_card
  have hsub : support weights \ S ⊆ support weights := Finset.sdiff_subset
  exact (Finset.ssubset_iff_of_subset hsub).mpr
    ⟨root, by simp [support, hroot], by simp [hmem]⟩

/-- Both strict balls include their root at every positive returned radius. -/
theorem root_mem_chosen {n : ℕ} (outDistance inDistance : Fin n → ℚ)
    (chooseDirection : ℚ → Bool) (r : ℚ) (root : Fin n)
    (hout : outDistance root = 0) (hin : inDistance root = 0) (hr : 0 < r) :
    root ∈ chosenBall outDistance inDistance chooseDirection r := by
  unfold chosenBall
  split_ifs <;> simp [ball, hout, hin, hr]

/-- A successful actual threshold search makes strict progress in its
 residual support measure. -/
theorem search_progress {n : ℕ} (capacity length : RegionVolume.Matrix n)
    (weights outDistance inDistance : Fin n → ℚ) (seed delta : ℚ) (p : ℕ)
    (root : Fin n) (r : ℚ)
    (hroot : 0 < weights root) (hout : outDistance root = 0) (hin : inDistance root = 0)
    (hd : 0 ≤ delta)
    (hs : RegionSearch.search capacity length outDistance inDistance seed delta p
      (direction weights outDistance inDistance) = some r) :
    (support (eraseWeights weights
      (chosenBall outDistance inDistance (direction weights outDistance inDistance) r))).card <
      (support weights).card := by
  exact support_decreases weights _ root hroot
    (root_mem_chosen outDistance inDistance _ r root hout hin
      (RegionSearch.search_radius capacity length outDistance inDistance seed delta p _ r hd hs).1)

end Lax455465Proofs.RegionSelection
