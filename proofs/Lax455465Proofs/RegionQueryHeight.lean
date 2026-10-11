import Lax455465Proofs.RegionQueryData
import Lax455465Proofs.VolumeHeight

namespace Lax455465Proofs.RegionQueryHeight

open RegionQueryData LpInputSize
open scoped NNRat

def exponent (n w : ℕ) : ℕ := 2*VolumeHeight.exponent n w+w+1

structure Bounds {n : ℕ} (q : Query n) (H : ℕ) : Prop where
  weightsBound : ∀ v, Height (2^H) (q.weights v : ℚ)
  capacityBound : ∀ u v, Height (2^H) (q.capacity u v : ℚ)
  lengthBound : ∀ u v, Height (2^H) (q.length u v : ℚ)
  distanceBound : ∀ b v, Height (2^H) (distance q b v : ℚ)
  seedBound : Height (2^H) (q.seed : ℚ)
  betaBound : Height (2^H) (q.beta : ℚ)
  radiusBound : Height (2^H) (q.radius : ℚ)
  volumeBounds : ∀ b, VolumeHeight.Bounds b q.capacity q.length (distance q b) q.seed q.radius H
  massPrefixBound : ∀ b i, Height (2^H)
    ((((RamMaskedSum.coefficients (List.ofFn q.weights) (BallMassData.mask (distance q b) q.radius)).take i).sum : ℚ≥0) : ℚ)
  boundaryPrefixBound : ∀ b i, Height (2^H)
    ((((RamMaskedSum.coefficients (MetricMatrix.values q.capacity) (MetricMatrix.values (BoundaryData.arcs b (distance q b) q.radius))).take i).sum : ℚ≥0) : ℚ)
  boundBound : Height (2^H) (bound q : ℚ)

/-- One polynomial bit exponent covers the whole acceptance query, with no
height accumulation across the repeated radius tests. -/
theorem bounds {n : ℕ} (q : Query n) (w : ℕ)
    (hw : ∀ v, Height (2^w) (q.weights v : ℚ))
    (hc : ∀ u v, Height (2^w) (q.capacity u v : ℚ))
    (hl : ∀ u v, Height (2^w) (q.length u v : ℚ))
    (hd : ∀ b v, Height (2^w) (distance q b v : ℚ))
    (hs : Height (2^w) (q.seed : ℚ)) (hb : Height (2^w) (q.beta : ℚ))
    (hr : Height (2^w) (q.radius : ℚ)) : Bounds q (exponent n w) := by
  let V := VolumeHeight.exponent n w
  let J := exponent n w
  have hwV : w ≤ V := by dsimp [V,VolumeHeight.exponent,VolumeHeight.sumExponent]; nlinarith
  have hVJ : V ≤ J := by dsimp [J,exponent,V]; omega
  have hwJ : w ≤ J := hwV.trans hVJ
  have hpow (a b : ℕ) (h : a ≤ b) : 2^a ≤ 2^b := Nat.pow_le_pow_right (by decide) h
  have widen {q : ℚ≥0} (h : Height (2^V) (q : ℚ)) : Height (2^J) (q : ℚ) := height_mono h (hpow _ _ hVJ)
  have vols (b : Bool) := VolumeHeight.bounds b q.capacity q.length (distance q b) q.seed q.radius w hc hl (hd b) hs hr
  have hvb (b : Bool) : VolumeHeight.Bounds b q.capacity q.length (distance q b) q.seed q.radius J := by
    have hv := vols b
    exact ⟨fun u v => widen (hv.capacityBound u v),fun u v => widen (hv.lengthBound u v),
      fun v => widen (hv.distanceBound v),widen hv.seedBound,widen hv.radiusBound,
      fun v => widen (hv.differenceBound v),fun u v => widen (hv.portionBound u v),
      fun a ha => widen (hv.coefficientBound a ha),fun i => widen (hv.prefixBound i),widen hv.valueBound⟩
  have hnn : n ≤ n*n := by
    by_cases hn : n=0
    · simp [hn]
    · have hn1 : 1≤n := by omega
      nlinarith
  have hmJ : w*(n+1)+n+1 ≤ J := by
    dsimp [J,exponent,V,VolumeHeight.exponent,VolumeHeight.sumExponent]
    nlinarith [Nat.mul_le_mul_left w hnn]
  have hcJ : w*(n*n+1)+n*n+1 ≤ J := by
    dsimp [J,exponent,V,VolumeHeight.exponent,VolumeHeight.sumExponent]
    nlinarith
  have hm (b : Bool) (i : ℕ) : Height (2^J)
      ((((RamMaskedSum.coefficients (List.ofFn q.weights) (BallMassData.mask (distance q b) q.radius)).take i).sum : ℚ≥0) : ℚ) := by
    have hh := MaskedMassData.prefix_height (List.ofFn q.weights) (BallMassData.mask (distance q b) q.radius) w
      (by intro a ha; obtain ⟨v,rfl⟩ := List.mem_ofFn.mp ha; exact hw v) i
    exact height_mono hh (by simpa only [List.length_ofFn] using hpow _ _ hmJ)
  have hbc (b : Bool) (i : ℕ) : Height (2^J)
      ((((RamMaskedSum.coefficients (MetricMatrix.values q.capacity) (MetricMatrix.values (BoundaryData.arcs b (distance q b) q.radius))).take i).sum : ℚ≥0) : ℚ) := by
    have hh := MaskedMassData.prefix_height (MetricMatrix.values q.capacity) (MetricMatrix.values (BoundaryData.arcs b (distance q b) q.radius)) w
      (by intro a ha; obtain ⟨v,rfl⟩ := List.mem_ofFn.mp ha; exact hc _ _) i
    exact height_mono hh (by simpa only [MetricMatrix.length_values] using hpow _ _ hcJ)
  refine ⟨fun v => height_mono (hw v) (hpow _ _ hwJ),fun u v => height_mono (hc u v) (hpow _ _ hwJ),
    fun u v => height_mono (hl u v) (hpow _ _ hwJ),fun b v => height_mono (hd b v) (hpow _ _ hwJ),
    height_mono hs (hpow _ _ hwJ),height_mono hb (hpow _ _ hwJ),height_mono hr (hpow _ _ hwJ),hvb,hm,hbc,?_⟩
  have hvol : Height (2^V) (volume q : ℚ) := (vols (direction q q.radius)).valueBound
  have hh := height_mul hb hvol
  have he : 2^w*2^V = 2^(w+V) := (Nat.pow_add 2 w V).symm
  have hsum : w+V ≤ J := by dsimp [J,exponent,V]; omega
  exact height_mono (by simpa only [bound,NNRat.coe_mul,he] using hh) (hpow _ _ hsum)

end Lax455465Proofs.RegionQueryHeight
