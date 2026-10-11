import Lax455465Proofs.VolumeData

namespace Lax455465Proofs.VolumeHeight

open LpInputSize MetricMatrix
open scoped NNRat

def sumExponent (n w : ℕ) : ℕ := 4*w*(n*n+1)+n*n+1
def exponent (n w : ℕ) : ℕ := 3*sumExponent n w+1

structure Bounds {n : ℕ} (outward : Bool) (capacity length : Matrix n)
    (distance : Fin n → ℚ≥0) (seed radius : ℚ≥0) (H : ℕ) : Prop where
  capacityBound : ∀ u v, Height (2^H) (capacity u v : ℚ)
  lengthBound : ∀ u v, Height (2^H) (length u v : ℚ)
  distanceBound : ∀ v, Height (2^H) (distance v : ℚ)
  seedBound : Height (2^H) (seed : ℚ)
  radiusBound : Height (2^H) (radius : ℚ)
  differenceBound : ∀ v, Height (2^H) (RamTruncatedSubtract.value radius (distance v) : ℚ)
  portionBound : ∀ u v, Height (2^H) (RamEdgePortion.value (length u v) (VolumeData.base outward distance u v) radius : ℚ)
  coefficientBound : ∀ q ∈ VolumeData.coefficients outward capacity length distance radius, Height (2^H) (q : ℚ)
  prefixBound : ∀ i, Height (2^H) ((((VolumeData.coefficients outward capacity length distance radius).take i).sum : ℚ≥0) : ℚ)
  valueBound : Height (2^H) (VolumeData.value outward capacity length distance seed radius : ℚ)

/-- A single exponent bounds all native intermediates, including the seed
addition. Its dependence on dimensions and input bit heights is polynomial. -/
theorem bounds {n : ℕ} (outward : Bool) (capacity length : Matrix n)
    (distance : Fin n → ℚ≥0) (seed radius : ℚ≥0) (w : ℕ)
    (hc : ∀ u v, Height (2^w) (capacity u v : ℚ))
    (hl : ∀ u v, Height (2^w) (length u v : ℚ))
    (hd : ∀ v, Height (2^w) (distance v : ℚ))
    (hs : Height (2^w) (seed : ℚ)) (hr : Height (2^w) (radius : ℚ)) :
    Bounds outward capacity length distance seed radius (exponent n w) := by
  have h4 : 4*w ≤ sumExponent n w := by dsimp [sumExponent]; nlinarith
  have hE : sumExponent n w ≤ exponent n w := by dsimp [exponent]; omega
  have hwE : w ≤ sumExponent n w := by omega
  have hwH : w ≤ exponent n w := hwE.trans hE
  have h3H : 3*w ≤ exponent n w := by omega
  have h4H : 4*w ≤ exponent n w := h4.trans hE
  have hpow (a b : ℕ) (h : a ≤ b) : 2^a ≤ 2^b := Nat.pow_le_pow_right (by decide) h
  have hM : 1 ≤ 2^w := by have := Nat.two_pow_pos w; omega
  have hdiff (v : Fin n) : Height (2^(3*w)) (RamTruncatedSubtract.value radius (distance v) : ℚ) := by
    simpa only [←Nat.pow_mul,show w*3=3*w by omega] using UnsignedHeight.clipped_bound hM hr (hd v)
  have hportion (u v : Fin n) : Height (2^(3*w)) (RamEdgePortion.value (length u v) (VolumeData.base outward distance u v) radius : ℚ) := by
    have hb : Height (2^w) (VolumeData.base outward distance u v : ℚ) := by cases outward <;> exact hd _
    have ht := UnsignedHeight.clipped_bound hM hr hb
    have hh := UnsignedHeight.min_bound (height_mono (hl u v) (by simpa using Nat.pow_le_pow_right hM (show 1≤3 by decide))) ht
    simpa only [RamEdgePortion.value,←Nat.pow_mul,show w*3=3*w by omega] using hh
  have hsum (i : ℕ) : Height (2^(sumExponent n w)) ((((VolumeData.coefficients outward capacity length distance radius).take i).sum : ℚ≥0) : ℚ) :=
    VolumeData.prefix_height outward capacity length distance radius w hc hl hd hr i
  have hfull : Height (2^(sumExponent n w)) (((VolumeData.coefficients outward capacity length distance radius).sum : ℚ≥0) : ℚ) := by
    simpa only [List.take_length] using hsum (VolumeData.coefficients outward capacity length distance radius).length
  refine ⟨fun u v => height_mono (hc u v) (hpow _ _ hwH),
    fun u v => height_mono (hl u v) (hpow _ _ hwH),fun v => height_mono (hd v) (hpow _ _ hwH),
    height_mono hs (hpow _ _ hwH),height_mono hr (hpow _ _ hwH),
    fun v => height_mono (hdiff v) (hpow _ _ h3H),
    fun u v => height_mono (hportion u v) (hpow _ _ h3H),
    fun q hq => height_mono (VolumeData.coefficient_height outward capacity length distance radius w hc hl hd hr q hq) (hpow _ _ h4H),
    fun i => height_mono (hsum i) (hpow _ _ hE),?_⟩
  have hh := UnsignedHeight.add_bound (by have := Nat.two_pow_pos (sumExponent n w); omega)
    (height_mono hs (hpow _ _ hwE)) hfull
  have heq : 2*(2^(sumExponent n w))^3 = 2^(exponent n w) := by
    rw [←Nat.pow_mul,show exponent n w=1+sumExponent n w*3 by dsimp [exponent]; omega,Nat.pow_add]
  simpa only [heq,VolumeData.value] using hh

end Lax455465Proofs.VolumeHeight
