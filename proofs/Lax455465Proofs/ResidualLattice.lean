import Lax455465Proofs.RationalSumHeight
import Lax455465Proofs.UnsignedHeight

namespace Lax455465Proofs.ResidualLattice
open scoped NNRat

/-- The denominator lattice is a proof invariant, not an extra RAM input.
All residual coordinates and bottleneck amounts remain in this lattice. -/
structure Bounded (D H : ℕ) (q : ℚ≥0) : Prop where
  denominator : q.den ∣ D
  value : (q : ℚ) ≤ H

theorem height {D H : ℕ} {q : ℚ≥0} (h : Bounded D H q) (hD : 0<D) (hH : 1≤H) :
    LpInputSize.Height (H*D) (q : ℚ) :=
  MetricHeight.height_of_denominator _ q.coe_nonneg H D hH hD
    (by simpa only [NNRat.den_coe] using h.denominator) h.value

theorem initial (qs : List ℚ≥0) (H : ℕ) (hnum : ∀ q∈qs,q.num≤H)
    (q : ℚ≥0) (hq : q∈qs) : Bounded (RationalSumHeight.denominator qs) H q := by
  refine ⟨RationalSumHeight.denominator_dvd qs q hq,?_⟩
  exact MetricHeight.value_bound (q : ℚ) q.coe_nonneg H
    (by simpa only [NNRat.natAbs_num_coe] using hnum q hq)

theorem zero (D H : ℕ) : Bounded D H 0 := by
  constructor <;> simp

theorem minimum {D H : ℕ} {a b : ℚ≥0} (ha : Bounded D H a) (hb : Bounded D H b) :
    Bounded D H (min a b) := by
  by_cases h : a≤b
  · simpa only [min_eq_left h] using ha
  · simpa only [min_eq_right (le_of_not_ge h)] using hb

/-- Exact clipped subtraction preserves the common denominator, avoiding
an exponential recurrence from separate local rational-height bounds. -/
theorem subtract {D H : ℕ} {a b : ℚ≥0} (ha : Bounded D H a) (hb : Bounded D H b) :
    Bounded D H (RamTruncatedSubtract.value a b) := by
  by_cases hab : (b : ℚ)≤(a : ℚ)
  · have he : (RamTruncatedSubtract.value a b : ℚ)=(a : ℚ)-(b : ℚ) := by
      simp only [RamTruncatedSubtract.value,NNRat.coe_mk,max_eq_left (sub_nonneg.mpr hab)]
    refine ⟨?_,?_⟩
    · have hh : ((a : ℚ)-(b : ℚ)).den ∣ D :=
        (Rat.sub_den_dvd_lcm _ _).trans (Nat.lcm_dvd
          (by simpa only [NNRat.den_coe] using ha.denominator)
          (by simpa only [NNRat.den_coe] using hb.denominator))
      simpa only [←he,NNRat.den_coe] using hh
    · rw [he]
      exact (sub_le_self _ b.coe_nonneg).trans ha.value
  · have he : RamTruncatedSubtract.value a b=0 := by
      apply Subtype.ext
      simp only [RamTruncatedSubtract.value,NNRat.coe_mk,NNRat.coe_zero,
        max_eq_right (sub_nonpos.mpr (le_of_not_ge hab))]
      rfl
    rw [he]
    exact zero D H

/-- A polynomial number of initial rational words gives a polynomial bit
bound for every subsequent residual, independently of the number of updates. -/
theorem dyadic_height (qs : List ℚ≥0) (w : ℕ)
    (hden : ∀ q∈qs,q.den≤2^w) {q : ℚ≥0}
    (hq : Bounded (RationalSumHeight.denominator qs) (2^w) q) :
    LpInputSize.Height (2^(w*(qs.length+1))) (q : ℚ) := by
  apply LpInputSize.height_mono (height hq (RationalSumHeight.denominator_pos qs)
    (Nat.succ_le_of_lt (Nat.two_pow_pos w)))
  calc
    2^w*RationalSumHeight.denominator qs≤2^w*2^(w*qs.length) :=
      Nat.mul_le_mul_left _ (RationalSumHeight.denominator_bound qs w hden)
    _=2^(w*(qs.length+1)) := by rw [←pow_add]; congr 1; ring

end Lax455465Proofs.ResidualLattice
