import Lax455465Proofs.RamArcMask
import Lax455465Proofs.BallMassData
import Lax455465Proofs.MetricCostData

namespace Lax455465Proofs.BoundaryData

open MetricMatrix
open scoped BigOperators NNRat

def vertices {n : ℕ} (distance : Fin n → ℚ≥0) (radius : ℚ≥0) : Fin n → Bool :=
  fun v => decide ((distance v : ℚ) < (radius : ℚ))

def arcs {n : ℕ} (outward : Bool) (distance : Fin n → ℚ≥0) (radius : ℚ≥0) : Matrix n :=
  RamArcMask.matrix (some outward) (vertices distance radius)

def value {n : ℕ} (outward : Bool) (capacity : Matrix n)
    (distance : Fin n → ℚ≥0) (radius : ℚ≥0) : ℚ≥0 :=
  (RamMaskedSum.coefficients (values capacity) (values (arcs outward distance radius))).sum

theorem masked_matrix {n : ℕ} (capacity flags : Matrix n) :
    RamMaskedSum.coefficients (values capacity) (values flags) =
      values (fun u v => if (flags u v).num=1 then capacity u v else 0) := by
  apply List.ext_getElem
  · simp only [RamMaskedSum.length_coefficients,length_values]
  · intro i hi hj
    have he : i < n*n := by simpa only [RamMaskedSum.length_coefficients,length_values] using hi
    rw [RamMaskedSum.coefficient_at (values capacity) (values flags) (by simp) i (by simpa using he)]
    simp only [values,List.getElem_ofFn]

theorem arc_condition {n : ℕ} (outward : Bool) (distance : Fin n → ℚ≥0)
    (radius : ℚ≥0) (u v : Fin n) :
    (arcs outward distance radius u v).num=1 ↔
      if outward then (distance u : ℚ)<radius ∧ (radius : ℚ)≤distance v
      else (distance v : ℚ)<radius ∧ (radius : ℚ)≤distance u := by
  unfold arcs RamArcMask.matrix RamBooleanArithmetic.bit RamBooleanArithmetic.flag vertices
  cases outward <;> by_cases hu : (distance u : ℚ)<radius <;> by_cases hv : (distance v : ℚ)<radius <;>
    simp [hu,hv,le_of_not_gt] <;> exact_mod_cast (by assumption)

/-- The sum of capacities selected by the native crossing mask equals the
strict left-limit boundary used by deterministic region growth. -/
theorem coe_value {n : ℕ} (outward : Bool) (capacity : Matrix n)
    (distance : Fin n → ℚ≥0) (radius : ℚ≥0) :
    (value outward capacity distance radius : ℚ) =
      RegionVolume.boundary (if outward then rational capacity else (fun u v => (capacity v u : ℚ)))
        (fun v => (distance v : ℚ)) (radius : ℚ) := by
  unfold value
  rw [masked_matrix]
  simp only [values,List.sum_ofFn]
  rw [←Equiv.sum_comp (DirectedFlowLP.edgeIndex n)]
  simp only [Equiv.symm_apply_apply,Fintype.sum_prod_type,NNRat.cast_sum]
  cases outward with
  | true =>
    simp only [RegionVolume.boundary]
    apply Finset.sum_congr rfl
    intro u hu
    apply Finset.sum_congr rfl
    intro v hv
    simp only [arc_condition,if_true,Bool.false_eq_true,if_false]
    split_ifs <;> rfl
  | false =>
    simp only [Bool.false_eq_true,if_false,RegionVolume.boundary]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u hu
    apply Finset.sum_congr rfl
    intro v hv
    simp only [arc_condition,if_true,Bool.false_eq_true,if_false]
    split_ifs <;> rfl

end Lax455465Proofs.BoundaryData
