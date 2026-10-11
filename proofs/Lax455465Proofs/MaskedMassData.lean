import Lax455465Proofs.RamMaskedSum
import Lax455465Proofs.RationalSumHeight
import Mathlib.Data.NNRat.BigOperators

namespace Lax455465Proofs.MaskedMassData

open LpInputSize
open scoped BigOperators NNRat

def flags {n : ℕ} (mask : Fin n → Bool) : List ℚ≥0 := List.ofFn fun v => if mask v then 1 else 0

theorem coefficients_ofFn {n : ℕ} (weights : Fin n → ℚ≥0) (mask : Fin n → Bool) :
    RamMaskedSum.coefficients (List.ofFn weights) (flags mask) =
      List.ofFn (fun v => if mask v then weights v else 0) := by
  apply List.ext_getElem
  · simp only [RamMaskedSum.length_coefficients,List.length_ofFn]
  · intro i hi hj
    have hn : i < n := by simpa only [RamMaskedSum.length_coefficients,List.length_ofFn] using hi
    rw [RamMaskedSum.coefficient_at (List.ofFn weights) (flags mask) (by simp [flags]) i (by simpa using hn)]
    simp only [flags,List.getElem_ofFn]
    cases h : mask ⟨i,hn⟩ <;> simp [h]

theorem coe_sum {n : ℕ} (weights : Fin n → ℚ≥0) (mask : Fin n → Bool) :
    (((RamMaskedSum.coefficients (List.ofFn weights) (flags mask)).sum : ℚ≥0) : ℚ) =
      ∑ v, if mask v then (weights v : ℚ) else 0 := by
  rw [coefficients_ofFn,List.sum_ofFn,NNRat.cast_sum]
  apply Finset.sum_congr rfl
  intro v hv
  cases mask v <;> rfl

theorem coefficient_height (qs ms : List ℚ≥0) (w : ℕ)
    (h : ∀ q ∈ qs, Height (2^w) (q : ℚ)) :
    ∀ q ∈ RamMaskedSum.coefficients qs ms, Height (2^w) (q : ℚ) := by
  intro q hq
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq
  split_ifs
  · exact h _ (List.getElem_mem i.isLt)
  · exact height_zero (by have := Nat.two_pow_pos w; omega)

/-- Masks do not increase the coordinate heights; one shared denominator
bounds every partial mass and boundary-capacity sum. -/
theorem prefix_height (qs ms : List ℚ≥0) (w : ℕ)
    (h : ∀ q ∈ qs, Height (2^w) (q : ℚ)) (i : ℕ) :
    Height (2^(w*(qs.length+1)+qs.length+1))
      ((((RamMaskedSum.coefficients qs ms).take i).sum : ℚ≥0) : ℚ) := by
  have hh := coefficient_height qs ms w h
  have hn : ∀ q ∈ RamMaskedSum.coefficients qs ms, q.num ≤ 2^w := by
    intro q hq
    simpa only [NNRat.natAbs_num_coe] using (hh q hq).1
  have hd : ∀ q ∈ RamMaskedSum.coefficients qs ms, q.den ≤ 2^w := by
    intro q hq
    simpa only [NNRat.den_coe] using (hh q hq).2
  simpa only [RamMaskedSum.length_coefficients] using RationalSumHeight.prefix_dyadic_height _ _ hn hd i

end Lax455465Proofs.MaskedMassData
