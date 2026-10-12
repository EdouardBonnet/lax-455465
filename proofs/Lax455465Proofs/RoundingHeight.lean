import Lax455465Proofs.RamMetricRounding
import Lax455465Proofs.RegionIterationHeight

namespace Lax455465Proofs.RoundingHeight
open Lax455465.RationalEncoding LpInputSize
open scoped NNRat

theorem cut_mono {n M N : ℕ} {I : RationalInstance n} {S : Finset (Fin n)}
    (h : CutScoreHeight.Bounds I S M) (hMN : M ≤ N) : CutScoreHeight.Bounds I S N := by
  exact ⟨fun v => height_mono (h.weightsBound v) hMN,fun u v => height_mono (h.capacityBound u v) hMN,
    fun i => height_mono (h.massPrefix i) hMN,fun i => height_mono (h.capacityPrefix i) hMN,
    height_mono h.totalBound hMN,height_mono h.massBound hMN,height_mono h.otherBound hMN,
    height_mono h.demandBound hMN,height_mono h.inverseBound hMN,height_mono h.cutCapacityBound hMN,
    height_mono h.ratioBound hMN⟩

theorem large_mono {n M N : ℕ} {I : RationalInstance n} {d : MetricMatrix.Matrix n}
    {Tin Tout : Finset (Fin n)} {hin : Tin.Nonempty} {hout : Tout.Nonempty}
    (h : LargePotentialData.Bounds I d Tin Tout hin hout M) (hMN : M ≤ N) :
    LargePotentialData.Bounds I d Tin Tout hin hout N := by
  exact ⟨fun v => height_mono (h.weights v) hMN,fun u v => height_mono (h.distances u v) hMN,
    fun q hq => height_mono (h.fromProducts q hq) hMN,fun q hq => height_mono (h.toProducts q hq) hMN,
    fun i => height_mono (h.fromPrefix i) hMN,fun i => height_mono (h.toPrefix i) hMN⟩

def cutExponent (n w : ℕ) : ℕ :=
  2*w+CutScoreHeight.exponent n w+LargePotentialData.exponent n w+2*n+4

/-- One polynomial bit exponent controls either potential, every candidate
cut score, and the bounded integer positions of every recorded history. -/
theorem cut_bounds {n : ℕ} (I : RationalInstance n) (d : MetricMatrix.Matrix n) (w p : ℕ) (hp : p ≤ n)
    (hw : ∀ v,Height (2^w) (I.weight v : ℚ)) (hc : ∀ u v,Height (2^w) (I.capacity u v : ℚ))
    (hd : ∀ u v,Height (2^w) (d u v : ℚ)) :
    (2^w)*(2^w) ≤ 2^(cutExponent n w) ∧ 2*p ≤ 2^(cutExponent n w) ∧
    (∀ S,CutScoreHeight.Bounds I S (2^(cutExponent n w))) ∧
    (∀ Tin Tout : Finset (Fin n),∀ hin : Tin.Nonempty,∀ hout : Tout.Nonempty,
      LargePotentialData.Bounds I d Tin Tout hin hout (2^(cutExponent n w))) := by
  have hpow (a : ℕ) (h : a ≤ cutExponent n w) : 2^a ≤ 2^(cutExponent n w) := Nat.pow_le_pow_right (by decide) h
  refine ⟨?_,?_,?_,?_⟩
  · rw [←Nat.pow_add]
    exact hpow _ (by dsimp [cutExponent]; omega)
  · calc
      2*p ≤ 2*n := by omega
      _ ≤ 2^(2*n) := Nat.lt_two_pow_self.le
      _ ≤ _ := hpow _ (by dsimp [cutExponent]; omega)
  · intro S
    exact cut_mono (CutScoreHeight.bounds I S w hw hc) (hpow _ (by dsimp [cutExponent]; omega))
  · intro Tin Tout hin hout
    exact large_mono (LargePotentialData.bounds I d Tin Tout hin hout w hw hd) (hpow _ (by dsimp [cutExponent]; omega))

def constantExponent (w : ℕ) : ℕ := 3*w+2

/-- Initial rational heights suffice for all computed region constants;
no numerical height assumption depends on a selected radius or cut. -/
theorem constant_bounds (cost total : ℚ≥0) (p w : ℕ) (hw : 2 ≤ w)
    (hc : Height (2^w) (cost : ℚ)) (ht : Height (2^w) (total : ℚ))
    (hp : p ≤ 2^w) (hk : RegionBudget.steps p ≤ 2^w) :
    RoundingConstantHeight.Bounds cost total p (2^(constantExponent w)) := by
  have h4 : 4 ≤ 2^w := (by norm_num : 4 ≤ 2^2).trans (Nat.pow_le_pow_right (by decide) hw)
  have he : 4*(2^w)^3=2^(constantExponent w) := by
    rw [constantExponent,Nat.mul_comm 3 w,pow_add,pow_mul]
    norm_num
    ring
  simpa only [he] using RoundingConstantHeight.bounds cost total p (2^w) h4 hc ht hp hk

end Lax455465Proofs.RoundingHeight
