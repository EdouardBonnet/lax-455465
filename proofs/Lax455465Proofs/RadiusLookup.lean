import Lax455465Proofs.RadiusData

namespace Lax455465Proofs.RadiusLookup
open scoped NNRat

theorem grid_at {n : ℕ} (outDistance inDistance : Fin n → ℚ≥0) (k : ℕ) (delta : ℚ≥0)
    (j : ℕ) (hj : j < k+1) :
    (RadiusData.candidates outDistance inDistance k delta)[j]'(by rw [RadiusData.length_candidates]; omega) = (delta/(k : ℚ≥0))*(j : ℚ≥0) := by
  unfold RadiusData.candidates
  rw [List.getElem_append_left (by simp only [List.length_append,List.length_map,List.length_range,List.length_ofFn]; omega),List.getElem_append_left (by simpa using hj)]
  all_goals simp

theorem out_at {n : ℕ} (outDistance inDistance : Fin n → ℚ≥0) (k : ℕ) (delta : ℚ≥0)
    (v : Fin n) :
    (RadiusData.candidates outDistance inDistance k delta)[k+1+v.val]'(by rw [RadiusData.length_candidates]; have := v.isLt; omega) = min delta (outDistance v) := by
  unfold RadiusData.candidates
  rw [List.getElem_append_left (by simp),List.getElem_append_right (by simp)]
  all_goals simp

theorem in_at {n : ℕ} (outDistance inDistance : Fin n → ℚ≥0) (k : ℕ) (delta : ℚ≥0)
    (v : Fin n) :
    (RadiusData.candidates outDistance inDistance k delta)[k+1+n+v.val]'(by rw [RadiusData.length_candidates]; have := v.isLt; omega) = min delta (inDistance v) := by
  unfold RadiusData.candidates
  rw [List.getElem_append_right (by simp)]
  all_goals simp

end Lax455465Proofs.RadiusLookup
