import Lax455465Proofs.RamArcMask
import Lax455465Proofs.MetricCostData
import Lax455465Proofs.RegionLoop

namespace Lax455465Proofs.ResidualData

open Lax455465.RationalEncoding MetricMatrix LpInputSize
open scoped NNRat

def mask {n : ℕ} (active : Finset (Fin n)) : Fin n → Bool := fun v => decide (v ∈ active)

def weights {n : ℕ} (I : RationalInstance n) (active : Finset (Fin n)) : Fin n → ℚ≥0 :=
  fun v => if v ∈ active then I.weight v else 0

def capacity {n : ℕ} (I : RationalInstance n) (active : Finset (Fin n)) : Matrix n :=
  fun u v => if u ∈ active ∧ v ∈ active then I.capacity u v else 0

theorem weight_products {n : ℕ} (I : RationalInstance n) (active : Finset (Fin n)) :
    RamProductSum.products (List.ofFn I.weight) (MaskedMassData.flags (mask active)) =
      List.ofFn (weights I active) := by
  apply List.ext_getElem
  · simp only [RamProductSum.products,List.length_ofFn]
  · intro i hi hj
    have hn : i < n := by simpa only [RamProductSum.products,List.length_ofFn] using hi
    rw [RamProductSum.value_at (List.ofFn I.weight) (MaskedMassData.flags (mask active)) (by simp [MaskedMassData.flags]) i (by simpa using hn)]
    simp only [List.getElem_ofFn,MaskedMassData.flags,mask,weights]
    split_ifs <;> simp_all

theorem capacity_products {n : ℕ} (I : RationalInstance n) (active : Finset (Fin n)) :
    RamProductSum.products (values I.capacity) (values (RamArcMask.matrix none (mask active))) =
      values (capacity I active) := by
  rw [MetricCostData.products_eq]
  congr 1
  funext u v
  simp only [capacity,RamArcMask.matrix,RamBooleanArithmetic.flag,RamBooleanArithmetic.bit,mask]
  by_cases hu : u ∈ active <;> by_cases hv : v ∈ active <;> simp [hu,hv]

theorem rational_weights {n : ℕ} (I : RationalInstance n) (active : Finset (Fin n)) :
    (fun v => (weights I active v : ℚ)) = RegionLoop.weights I active := by
  funext v
  unfold weights RegionLoop.weights
  split_ifs <;> rfl

theorem rational_capacity {n : ℕ} (I : RationalInstance n) (active : Finset (Fin n)) :
    rational (capacity I active) = RegionLoop.capacity I active := by
  funext u v
  dsimp only [capacity,rational,RegionLoop.capacity]
  split_ifs <;> rfl

/-- Reconstructing residual arrays from the original input and zero/one
membership does not increase any rational coordinate height. -/
theorem weights_height {n : ℕ} (I : RationalInstance n) (active : Finset (Fin n)) (w : ℕ)
    (h : ∀ v, Height (2^w) (I.weight v : ℚ)) :
    ∀ v, Height (2^w) (weights I active v : ℚ) := by
  intro v
  unfold weights
  split_ifs
  · exact h v
  · exact height_zero (by have := Nat.two_pow_pos w; omega)

theorem capacity_height {n : ℕ} (I : RationalInstance n) (active : Finset (Fin n)) (w : ℕ)
    (h : ∀ u v, Height (2^w) (I.capacity u v : ℚ)) :
    ∀ u v, Height (2^w) (capacity I active u v : ℚ) := by
  intro u v
  unfold capacity
  split_ifs
  · exact h u v
  · exact height_zero (by have := Nat.two_pow_pos w; omega)

end Lax455465Proofs.ResidualData
