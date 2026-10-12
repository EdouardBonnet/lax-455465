import Lax455465Proofs.CutScoreData

namespace Lax455465Proofs.CutScoreHeight
open Lax455465.RationalEncoding LpInputSize CutScoreData
open scoped NNRat

def sumExponent (n w : ℕ) : ℕ := w*(n*n+1)+n*n+1
def exponent (n w : ℕ) : ℕ := 3*sumExponent n w

structure Bounds {n : ℕ} (I : RationalInstance n) (S : Finset (Fin n)) (M : ℕ) : Prop where
  weightsBound : ∀ v, Height M (I.weight v : ℚ)
  capacityBound : ∀ u v, Height M (I.capacity u v : ℚ)
  massPrefix : ∀ i, Height M ((((RamMaskedSum.coefficients (List.ofFn I.weight) (vertexFlags S)).take i).sum : ℚ≥0) : ℚ)
  capacityPrefix : ∀ i, Height M ((((RamMaskedSum.coefficients (MetricMatrix.values I.capacity) (MetricMatrix.values (arcFlags S))).take i).sum : ℚ≥0) : ℚ)
  totalBound : Height M (RamRoundingInit.total I.weight : ℚ)
  massBound : Height M (mass I S : ℚ)
  otherBound : Height M (otherMass I S : ℚ)
  demandBound : Height M (demand I S : ℚ)
  inverseBound : Height M (((demand I S)⁻¹ : ℚ≥0) : ℚ)
  cutCapacityBound : Height M (capacity I S : ℚ)
  ratioBound : Height M (ratio I S : ℚ)

/-- All cuts share one polynomial word-width bound: masked sums use the
original input denominator lattice, and demand and ratio add only fixed-depth
rational arithmetic. No height bound depends on which shore is selected. -/
theorem bounds {n : ℕ} (I : RationalInstance n) (S : Finset (Fin n)) (w : ℕ)
    (hw : ∀ v, Height (2^w) (I.weight v : ℚ))
    (hc : ∀ u v, Height (2^w) (I.capacity u v : ℚ)) : Bounds I S (2^(exponent n w)) := by
  let V := sumExponent n w
  let H := exponent n w
  have hn : n≤n*n := by
    by_cases hz : n=0
    · simp [hz]
    · have hn1 : 1≤n := by omega
      nlinarith
  have hmV : w*(n+1)+n+1≤V := by
    dsimp [V,sumExponent]
    nlinarith [Nat.mul_le_mul_left w hn]
  have hwV : w≤V := by dsimp [V,sumExponent]; nlinarith
  have hVH : V≤H := by dsimp [V,H,exponent]; omega
  have widen {q : ℚ} (h : Height (2^V) q) : Height (2^H) q := height_mono h (Nat.pow_le_pow_right (by decide) hVH)
  have massPre (T : Finset (Fin n)) (i : ℕ) : Height (2^V)
      ((((RamMaskedSum.coefficients (List.ofFn I.weight) (vertexFlags T)).take i).sum : ℚ≥0) : ℚ) := by
    have h := MaskedMassData.prefix_height (List.ofFn I.weight) (vertexFlags T) w
      (by intro a ha; obtain ⟨v,rfl⟩ := List.mem_ofFn.mp ha; exact hw v) i
    exact height_mono h (by simpa only [List.length_ofFn] using Nat.pow_le_pow_right (by decide : 1≤2) hmV)
  have capPre (i : ℕ) : Height (2^V)
      ((((RamMaskedSum.coefficients (MetricMatrix.values I.capacity) (MetricMatrix.values (arcFlags S))).take i).sum : ℚ≥0) : ℚ) := by
    simpa only [MetricMatrix.length_values,V,sumExponent] using MaskedMassData.prefix_height (MetricMatrix.values I.capacity)
      (MetricMatrix.values (arcFlags S)) w
      (by intro a ha; obtain ⟨v,rfl⟩ := List.mem_ofFn.mp ha; exact hc _ _) i
  have hmass (T : Finset (Fin n)) : Height (2^V) (mass I T : ℚ) := by
    simpa only [List.take_length,mass] using massPre T (RamMaskedSum.coefficients (List.ofFn I.weight) (vertexFlags T)).length
  have hcap : Height (2^V) (capacity I S : ℚ) := by
    simpa only [List.take_length,capacity] using capPre (RamMaskedSum.coefficients (MetricMatrix.values I.capacity) (MetricMatrix.values (arcFlags S))).length
  have hother : Height (2^V) (otherMass I S : ℚ) := by rw [otherMass_eq]; exact hmass _
  have htotal : Height (2^V) (RamRoundingInit.total I.weight : ℚ) := by
    have h := RationalSumHeight.prefix_dyadic_height (List.ofFn I.weight) w
      (by intro a ha; obtain ⟨v,rfl⟩ := List.mem_ofFn.mp ha; simpa only [NNRat.natAbs_num_coe] using (hw v).1)
      (by intro a ha; obtain ⟨v,rfl⟩ := List.mem_ofFn.mp ha; simpa only [NNRat.den_coe] using (hw v).2) n
    have htake : (List.ofFn I.weight).take n=List.ofFn I.weight := by simp
    apply height_mono (by simpa only [htake,RamRoundingInit.total] using h)
    simpa only [List.length_ofFn] using Nat.pow_le_pow_right (by decide : 1≤2) hmV
  have hd : Height (2^(2*V)) (demand I S : ℚ) := by
    have hh := height_mul (hmass S) hother
    simpa only [demand,NNRat.coe_mul,←Nat.pow_add,show V+V=2*V by omega] using hh
  have hi : Height (2^(2*V)) (((demand I S)⁻¹ : ℚ≥0) : ℚ) := RoundingConstants.inverse_height Nat.one_le_two_pow hd
  have hratio : Height (2^H) (ratio I S : ℚ) := by
    have hh := height_mul hcap hi
    simpa only [ratio,div_eq_mul_inv,NNRat.coe_mul,NNRat.coe_inv,←Nat.pow_add,H,exponent,V,show sumExponent n w+2*sumExponent n w=3*sumExponent n w by omega] using hh
  have widen2 {q : ℚ} (h : Height (2^(2*V)) q) : Height (2^H) q :=
    height_mono h (Nat.pow_le_pow_right (by decide) (by dsimp [H,exponent,V]; omega))
  exact ⟨fun v => height_mono (hw v) (Nat.pow_le_pow_right (by decide) (hwV.trans hVH)),
    fun u v => height_mono (hc u v) (Nat.pow_le_pow_right (by decide) (hwV.trans hVH)),
    fun i => widen (massPre S i),fun i => widen (capPre i),widen htotal,widen (hmass S),widen hother,
    widen2 hd,widen2 hi,widen hcap,hratio⟩

end Lax455465Proofs.CutScoreHeight
