import Lax455465Proofs.RegionRounding
import Lax455465Proofs.ZeroCostRounding

open scoped BigOperators NNReal NNRat

namespace Lax455465Proofs.MetricRounding

open Lax455465.RationalEncoding Lax455465.ProductNetwork CutSweeps RationalDistances RegionRounding

def round {n : ℕ} (I : RationalInstance n) (d : Distance n) : Option (Finset (Fin n)) :=
  if metricCost I d = 0 then ZeroCostRounding.round I d else positiveRound I d

/-- The algorithm computes rational support membership; it agrees with
the positive-weight count in the public real specification. -/
theorem supportSize_eq {n : ℕ} (I : RationalInstance n) : supportSize I = supportCount I.weights := by
  unfold supportSize RegionSelection.support supportCount
  congr 1
  ext v
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, RegionLoop.weights, ↓reduceIte]
  change (0 : ℚ) < (I.weight v : ℚ) ↔ (0 : ℝ≥0) < (I.weight v : ℝ≥0)
  norm_cast

theorem total_positive {n : ℕ} (I : RationalInstance n) (hp : 0 < supportSize I) :
    0 < LargeBallRounding.total I := by
  obtain ⟨v, hv⟩ := Finset.card_pos.mp hp
  have hroot := (Finset.mem_filter.mp hv).2
  have hpositive : 0 < (I.weight v : ℚ) := hroot.trans_le (RegionLoop.weights_le I Finset.univ v)
  exact hpositive.trans_le (Finset.single_le_sum (fun u _ => NNRat.coe_nonneg (I.weight u)) (Finset.mem_univ v))

/-- The complete deterministic rational rounding routine succeeds,
including disconnected and zero-cost metric inputs. -/
theorem round_correct {n : ℕ} (I : RationalInstance n) (d : Distance n)
    (hp : 2 ≤ supportSize I) (hd : Nonnegative d) (hdiag : ∀ v, d v v = 0)
    (hsep : 1 ≤ LargeBallRounding.distanceSeparation I d) (htri : ∀ u v w, d u w ≤ d u v + d v w) :
    ∃ S, round I d = some S ∧ admissibleQ I S ∧
      ratioQ I S ≤ (288 / 5 : ℚ) * (RegionBudget.steps (supportSize I) : ℚ) * metricCost I d := by
  have hW : 0 ≤ metricCost I d :=
    RegionCharging.weight_nonnegative _ d (fun u v => NNRat.coe_nonneg _) hd
  by_cases hz : metricCost I d = 0
  · obtain ⟨S, hs, hadm, hratio⟩ := ZeroCostRounding.round_correct I d hd hdiag htri hsep hz
    refine ⟨S, by simp only [round, if_pos hz, hs], hadm, ?_⟩
    simpa only [hz, mul_zero] using hratio
  · obtain ⟨S, hs, hadm, hratio⟩ := positiveRound_correct I d (total_positive I (by omega)) hp
      hd hdiag hsep htri (lt_of_le_of_ne hW (Ne.symm hz))
    exact ⟨S, by simp only [round, if_neg hz, hs], hadm, hratio⟩

/-- Integer bit-length budgeting gives the advertised O(log₂ p) bound.
The proof uses one fixed universal constant, independent of all data. -/
theorem round_log_bound {n : ℕ} (I : RationalInstance n) (d : Distance n)
    (hp : 2 ≤ supportCount I.weights) (hd : Nonnegative d) (hdiag : ∀ v, d v v = 0)
    (hsep : 1 ≤ LargeBallRounding.distanceSeparation I d) (htri : ∀ u v w, d u w ≤ d u v + d v w) :
    ∃ S, round I d = some S ∧ admissibleQ I S ∧
      (ratioQ I S : ℝ) ≤ 512 * (Real.log (supportCount I.weights) / Real.log 2) * (metricCost I d : ℝ) := by
  have hpq : 2 ≤ supportSize I := by simpa only [supportSize_eq] using hp
  obtain ⟨S, hs, hadm, hratio⟩ := round_correct I d hpq hd hdiag hsep htri
  refine ⟨S, hs, hadm, ?_⟩
  have hratioR : (ratioQ I S : ℝ) ≤
      (((288 / 5 : ℚ) * (RegionBudget.steps (supportSize I) : ℚ) * metricCost I d : ℚ) : ℝ) :=
    Rat.cast_le.mpr hratio
  norm_num only [Rat.cast_mul, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] at hratioR
  have hlog := RegionBudget.steps_le_log (supportSize I) hpq
  have hlogpos : 0 ≤ Real.log (supportSize I) / Real.log 2 := by
    positivity
  have hW : 0 ≤ (metricCost I d : ℝ) := by
    exact_mod_cast RegionCharging.weight_nonnegative (fun u v => (I.capacity u v : ℚ)) d
      (fun u v => NNRat.coe_nonneg _) hd
  have hbudget := mul_le_mul_of_nonneg_left hlog (show (0 : ℝ) ≤ 288 / 5 by norm_num)
  have hbudgetW := mul_le_mul_of_nonneg_right hbudget hW
  rw [supportSize_eq] at hratioR hbudgetW hlogpos
  have hlogW := mul_nonneg hlogpos hW
  nlinarith

end Lax455465Proofs.MetricRounding
