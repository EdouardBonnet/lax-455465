import Lax455465Proofs.RamTruncatedSubtract
import Lax455465Proofs.MetricHeight

namespace Lax455465Proofs.UnsignedHeight

open LpInputSize
open scoped NNRat

abbrev Bounded (M : ℕ) (q : ℚ≥0) := Height M (q : ℚ)

theorem min_bound {M : ℕ} {a b : ℚ≥0} (ha : Bounded M a) (hb : Bounded M b) :
    Bounded M (min a b) := by
  by_cases hab : a ≤ b
  · simpa only [min_eq_left hab] using ha
  · simpa only [min_eq_right (le_of_not_ge hab)] using hb

theorem max_bound {M : ℕ} {a b : ℚ≥0} (ha : Bounded M a) (hb : Bounded M b) :
    Bounded M (max a b) := by
  by_cases hab : a ≤ b
  · simpa only [max_eq_right hab] using hb
  · simpa only [max_eq_left (le_of_not_ge hab)] using ha

theorem mul_bound {M N : ℕ} {a b : ℚ≥0} (ha : Bounded M a) (hb : Bounded N b) :
    Bounded (M*N) (a*b) := by
  simpa only [Bounded,NNRat.coe_mul] using height_mul ha hb

/-- Fixed-depth clipped arithmetic has polynomial bit height. Longer sums
use the separate common-denominator invariant rather than this local bound. -/
theorem clipped_bound {M : ℕ} {a b : ℚ≥0} (hM : 1 ≤ M) (ha : Bounded M a) (hb : Bounded M b) :
    Bounded (M^3) (RamTruncatedSubtract.value a b) := by
  by_cases hab : (b : ℚ) ≤ (a : ℚ)
  · have hden : ((a : ℚ)-(b : ℚ)).den ∣ a.den*b.den := by
      simpa only [NNRat.den_coe] using Rat.sub_den_dvd (a : ℚ) (b : ℚ)
    have hval : (a : ℚ)-(b : ℚ) ≤ (M : ℚ) := by
      have hv := MetricHeight.value_bound (a : ℚ) a.coe_nonneg M ha.1
      linarith [b.coe_nonneg]
    have hh := MetricHeight.height_of_denominator _ (sub_nonneg.mpr hab) M (a.den*b.den) hM
      (Nat.mul_pos a.den_pos b.den_pos) hden hval
    have hp : a.den*b.den ≤ M*M := Nat.mul_le_mul ha.2 hb.2
    have hm : M*(a.den*b.den) ≤ M^3 := by nlinarith [Nat.mul_le_mul_left M hp]
    have hheight := height_mono hh hm
    simpa only [Bounded,RamTruncatedSubtract.value,NNRat.coe_mk,max_eq_left (sub_nonneg.mpr hab)] using hheight
  · have hm : 1 ≤ M^3 := by simpa using (Nat.pow_le_pow_left hM 3)
    simpa only [Bounded,RamTruncatedSubtract.value,NNRat.coe_mk,max_eq_right (sub_nonpos.mpr (le_of_not_ge hab))] using height_zero hm

theorem add_bound {M : ℕ} {a b : ℚ≥0} (hM : 1 ≤ M) (ha : Bounded M a) (hb : Bounded M b) :
    Bounded (2*M^3) (a+b) := by
  have hden : ((a : ℚ)+(b : ℚ)).den ∣ a.den*b.den := by
    simpa only [NNRat.den_coe] using Rat.add_den_dvd (a : ℚ) (b : ℚ)
  have hval : (a : ℚ)+(b : ℚ) ≤ (2*M : ℕ) := by
    have hva := MetricHeight.value_bound (a : ℚ) a.coe_nonneg M ha.1
    have hvb := MetricHeight.value_bound (b : ℚ) b.coe_nonneg M hb.1
    push_cast
    linarith
  have hh := MetricHeight.height_of_denominator _ (add_nonneg a.coe_nonneg b.coe_nonneg) (2*M)
    (a.den*b.den) (by omega) (Nat.mul_pos a.den_pos b.den_pos) hden hval
  have hp : a.den*b.den ≤ M*M := Nat.mul_le_mul ha.2 hb.2
  exact height_mono hh (by nlinarith [Nat.mul_le_mul_left (2*M) hp])

end Lax455465Proofs.UnsignedHeight
