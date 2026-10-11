import Lax455465Proofs.RamEdgePortion
import Lax455465Proofs.MetricCostData
import Lax455465Proofs.RationalSumHeight
import Lax455465Proofs.UnsignedHeight

namespace Lax455465Proofs.VolumeData

open MetricMatrix LpInputSize
open scoped BigOperators NNRat

def base {n : ℕ} (outward : Bool) (distance : Fin n → ℚ≥0) (u v : Fin n) : ℚ≥0 :=
  if outward then distance u else distance v

def coefficients {n : ℕ} (outward : Bool) (capacity length : Matrix n)
    (distance : Fin n → ℚ≥0) (radius : ℚ≥0) : List ℚ≥0 :=
  values (fun u v => capacity u v * RamEdgePortion.value (length u v) (base outward distance u v) radius)

def value {n : ℕ} (outward : Bool) (capacity length : Matrix n)
    (distance : Fin n → ℚ≥0) (seed radius : ℚ≥0) : ℚ≥0 :=
  seed + (coefficients outward capacity length distance radius).sum

/-- The exact clipped edge sum, in original arc order, is the volume for
an outward ball or the transposed volume for an inward ball. -/
theorem coe_value {n : ℕ} (outward : Bool) (capacity length : Matrix n)
    (distance : Fin n → ℚ≥0) (seed radius : ℚ≥0) :
    (value outward capacity length distance seed radius : ℚ) =
      RegionVolume.volume (if outward then rational capacity else fun u v => (capacity v u : ℚ))
        (if outward then rational length else fun u v => (length v u : ℚ))
        (fun v => (distance v : ℚ)) seed radius := by
  unfold value coefficients
  simp only [values,List.sum_ofFn,NNRat.coe_add,NNRat.cast_sum,NNRat.coe_mul,RamEdgePortion.coe_value]
  rw [←Equiv.sum_comp (DirectedFlowLP.edgeIndex n)]
  simp only [Equiv.symm_apply_apply,Fintype.sum_prod_type]
  cases outward with
  | true => rfl
  | false =>
    simp only [base,Bool.false_eq_true,if_false,RegionVolume.volume]
    rw [Finset.sum_comm]

/-- Fixed-depth clipping and multiplication preserve polynomial bit height;
partial sums share one common denominator. -/
theorem coefficient_height {n : ℕ} (outward : Bool) (capacity length : Matrix n)
    (distance : Fin n → ℚ≥0) (radius : ℚ≥0) (w : ℕ)
    (hc : ∀ u v, Height (2^w) (capacity u v : ℚ))
    (hl : ∀ u v, Height (2^w) (length u v : ℚ))
    (hd : ∀ v, Height (2^w) (distance v : ℚ)) (hr : Height (2^w) (radius : ℚ)) :
    ∀ q ∈ coefficients outward capacity length distance radius, Height (2^(4*w)) (q : ℚ) := by
  intro q hq
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq
  let uv := (DirectedFlowLP.edgeIndex n).symm i
  have hb : Height (2^w) (base outward distance uv.1 uv.2 : ℚ) := by
    cases outward <;> exact hd _
  have hm : 1 ≤ 2^w := by have := Nat.two_pow_pos w; omega
  have hpow : 2^w ≤ (2^w)^3 := by simpa using Nat.pow_le_pow_right hm (show 1 ≤ 3 by decide)
  have hp := UnsignedHeight.min_bound (height_mono (hl uv.1 uv.2) hpow) (UnsignedHeight.clipped_bound hm hr hb)
  have hh := height_mul (hc uv.1 uv.2) hp
  simpa only [uv,RamEdgePortion.value,NNRat.coe_mul,←Nat.pow_mul,←Nat.pow_add,
    show w+w*3=4*w by omega] using hh

theorem prefix_height {n : ℕ} (outward : Bool) (capacity length : Matrix n)
    (distance : Fin n → ℚ≥0) (radius : ℚ≥0) (w : ℕ)
    (hc : ∀ u v, Height (2^w) (capacity u v : ℚ))
    (hl : ∀ u v, Height (2^w) (length u v : ℚ))
    (hd : ∀ v, Height (2^w) (distance v : ℚ)) (hr : Height (2^w) (radius : ℚ)) (i : ℕ) :
    Height (2^(4*w*(n*n+1)+n*n+1))
      ((((coefficients outward capacity length distance radius).take i).sum : ℚ≥0) : ℚ) := by
  have hh := coefficient_height outward capacity length distance radius w hc hl hd hr
  have hn : ∀ q ∈ coefficients outward capacity length distance radius, q.num ≤ 2^(4*w) := by
    intro q hq; simpa only [NNRat.natAbs_num_coe] using (hh q hq).1
  have hd : ∀ q ∈ coefficients outward capacity length distance radius, q.den ≤ 2^(4*w) := by
    intro q hq; simpa only [NNRat.den_coe] using (hh q hq).2
  simpa only [coefficients,length_values] using RationalSumHeight.prefix_dyadic_height _ _ hn hd i

end Lax455465Proofs.VolumeData
