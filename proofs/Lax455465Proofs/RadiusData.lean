import Lax455465Proofs.RegionSearch
import Lax455465Proofs.UnsignedHeight
import Mathlib.Data.NNRat.BigOperators

namespace Lax455465Proofs.RadiusData

open LpInputSize
open scoped NNRat

def candidates {n : ℕ} (outDistance inDistance : Fin n → ℚ≥0) (k : ℕ) (delta : ℚ≥0) : List ℚ≥0 :=
  (List.range (k+1)).map (fun j : ℕ => (delta/(k : ℚ≥0))*(j : ℚ≥0)) ++
    List.ofFn (fun v => min delta (outDistance v)) ++ List.ofFn (fun v => min delta (inDistance v))

@[simp] theorem length_candidates {n : ℕ} (outDistance inDistance : Fin n → ℚ≥0) (k : ℕ) (delta : ℚ≥0) :
    (candidates outDistance inDistance k delta).length=k+1+2*n := by
  simp [candidates]; omega

/-- The row-order radius buffer is exactly the unsorted event/grid list
whose search guarantee is proved by finite rational volume growth. -/
theorem coe_candidates {n : ℕ} (outDistance inDistance : Fin n → ℚ≥0) (k : ℕ) (delta : ℚ≥0) :
    (candidates outDistance inDistance k delta).map (fun q : ℚ≥0 => (q : ℚ)) =
      RegionSearch.candidates (fun v => (outDistance v : ℚ)) (fun v => (inDistance v : ℚ)) k delta := by
  simp only [candidates,List.map_append,List.map_map,List.map_ofFn,RegionSearch.candidates,Function.comp_apply,NNRat.coe_min]
  congr 2
  · apply List.map_congr_left
    intro j hj
    simp only [Function.comp_apply,NNRat.coe_mul,NNRat.coe_div,NNRat.coe_natCast,RegionSearch.grid]
    ring
  · congr 1
    funext v
    simp [max_eq_left (outDistance v).coe_nonneg]
  · funext v
    simp [max_eq_left (inDistance v).coe_nonneg]

/-- Each candidate uses at most one multiplication beyond the stored grid
unit. Clipping vertex events preserves their coordinate heights. -/
theorem height {n : ℕ} (outDistance inDistance : Fin n → ℚ≥0) (k M : ℕ) (delta : ℚ≥0)
    (hM : 1≤M) (hk : k≤M) (hu : Height M ((delta/(k : ℚ≥0) : ℚ≥0) : ℚ))
    (hd : Height M (delta : ℚ))
    (ho : ∀ v, Height M (outDistance v : ℚ)) (hi : ∀ v, Height M (inDistance v : ℚ)) :
    ∀ q ∈ candidates outDistance inDistance k delta, Height (M*M) (q : ℚ) := by
  intro q hq
  simp only [candidates,List.mem_append] at hq
  rcases hq with (hq|hq)|hq
  · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hq
    have hjk : j≤k := by have := List.mem_range.mp hj; omega
    have hjh : Height M ((j : ℚ≥0) : ℚ) := by
      simp only [NNRat.coe_natCast,Rat.num_natCast,Rat.den_natCast,Int.natAbs_natCast]
      exact ⟨hjk.trans hk,hM⟩
    simpa only [NNRat.coe_mul] using height_mul hu hjh
  · obtain ⟨v,rfl⟩ := List.mem_ofFn.mp hq
    exact height_mono (UnsignedHeight.min_bound hd (ho v)) (by nlinarith)
  · obtain ⟨v,rfl⟩ := List.mem_ofFn.mp hq
    exact height_mono (UnsignedHeight.min_bound hd (hi v)) (by nlinarith)

end Lax455465Proofs.RadiusData
