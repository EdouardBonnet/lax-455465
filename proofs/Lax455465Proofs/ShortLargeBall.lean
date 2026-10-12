import Lax455465Proofs.RegionRounding
import Lax455465Proofs.UniformCutBounds

open scoped BigOperators
namespace Lax455465Proofs.ShortLargeBall
open Lax455465.RationalEncoding RegionLoop RegionHistory CutSweeps RationalDistances RegionRounding

/-- A metric whose total capacity-weighted length is small compared with
the sparsest cut must contain a large root ball. This uses the completed
region-history charging proof and needs no metric-separation assumption. -/
theorem exists_large {n : ℕ} (I : RationalInstance n) (d : Distance n)
    (s : ℚ) (hcut : UniformCutBounds.CutLower I s)
    (hM : 0 < LargeBallRounding.total I) (hp : 2 ≤ supportSize I)
    (hd : Nonnegative d) (hdiag : ∀ v,d v v=0)
    (htri : ∀ u v w,d u w ≤ d u v+d v w) (hW : 0 < metricCost I d)
    (hcheap : (288/5 : ℚ)*(RegionBudget.steps (supportSize I) : ℚ)*metricCost I d < s) :
    ∃ R : Region n,LargeGood I d (radiusBudget I) R := by
  have hp0 : 0 < supportSize I := by omega
  have hpq : (0 : ℚ) < supportSize I := by exact_mod_cast hp0
  have hdelta : 0 < radiusBudget I := by unfold radiusBudget; positivity
  have hseed : 0 < metricCost I d / supportSize I := div_pos hW hpq
  have hcost : metricCost I d ≤ (supportSize I : ℚ) * (metricCost I d / supportSize I) := by
    rw [mul_div_cancel₀ _ (ne_of_gt hpq)]
  obtain ⟨result,_,hvalid⟩ := run_correct I d (metricCost I d / supportSize I) (radiusBudget I)
    (supportSize I) (supportSize I) hd hdiag htri hseed hdelta hp0 hcost Finset.univ le_rfl
  cases result with
  | large R => exact ⟨R,hvalid⟩
  | regions history =>
    have hc := HistoryCharging.total_charge I d (radiusBudget I) (supportSize I) history hp0 hvalid.2 hdelta hd hvalid.1
    have heq : 2 * RegionSearch.slope (RegionBudget.steps (supportSize I)) (radiusBudget I) * metricCost I d =
        8 * (RegionBudget.steps (supportSize I) : ℚ) * BalancedRegionCut.total I ^ 2 * metricCost I d := by
      unfold RegionSearch.slope radiusBudget
      change 2 * ((RegionBudget.steps (supportSize I) : ℚ) / (1 / (4 * LargeBallRounding.total I ^ 2))) * metricCost I d =
        8 * (RegionBudget.steps (supportSize I) : ℚ) * LargeBallRounding.total I ^ 2 * metricCost I d
      field_simp [ne_of_gt hM]
      ring
    change (∑ j : Fin history.length, RegionOrdering.chargedBoundary (fun u v => (I.capacity u v : ℚ))
      (index d history) (orientation history) j) ≤
        2 * RegionSearch.slope (RegionBudget.steps (supportSize I)) (radiusBudget I) * metricCost I d at hc
    rw [heq] at hc
    obtain ⟨S, hs, hadm, hratio⟩ := BalancedRegionCut.round_ratio I (index d history) (orientation history)
      (RegionBudget.steps (supportSize I)) (metricCost I d) hM (Nat.cast_nonneg _) hW.le
      (blocks_small I d _ _ _ history hvalid.1 hM) hc
    exact (not_lt_of_ge ((hcut S hadm).trans hratio) hcheap).elim

end Lax455465Proofs.ShortLargeBall
