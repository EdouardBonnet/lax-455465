import Mathlib.Tactic

open scoped BigOperators

namespace Lax455465Proofs.BalancedPrefix

def prefixMass (weights : ℕ → ℚ) (t : ℕ) : ℚ := ∑ j ∈ Finset.range (t + 1), weights j

/-- First threshold whose low-position prefix has at least one sixth of the total mass. -/
def choose (weights : ℕ → ℚ) (limit : ℕ) (total : ℚ) : Option ℕ :=
  (List.range limit).find? fun t => decide (total / 6 ≤ prefixMass weights t)

/-- Small blocks force the actual finite scan to stop before its prefix
can exceed five sixths of the total mass. -/
theorem choose_correct (weights : ℕ → ℚ) (limit : ℕ) (total : ℚ)
    (hpos : 0 < total) (hsum : (∑ j ∈ Finset.range limit, weights j) = total)
    (hsmall : ∀ j < limit, weights j < (2 / 3 : ℚ) * total) :
    ∃ t, choose weights limit total = some t ∧ t < limit ∧
      total / 6 ≤ prefixMass weights t ∧ prefixMass weights t < (5 / 6 : ℚ) * total := by
  have hlimit : 0 < limit := by
    by_contra h
    have hzero : limit = 0 := by omega
    simp only [hzero, Finset.range_zero, Finset.sum_empty] at hsum
    linarith
  have hlast : prefixMass weights (limit - 1) = total := by
    unfold prefixMass
    rw [Nat.sub_add_cancel (by omega), hsum]
  cases hs : choose weights limit total with
  | none =>
    unfold choose at hs
    have hfail := List.find?_eq_none.mp hs (limit - 1) (List.mem_range.mpr (by omega))
    simp only [decide_eq_true_eq] at hfail
    exact False.elim (hfail (by rw [hlast]; linarith))
  | some t =>
    have ht : t < limit := List.mem_range.mp (List.mem_of_find?_eq_some hs)
    have hfound : total / 6 ≤ prefixMass weights t := by
      simpa only [decide_eq_true_eq] using List.find?_some hs
    refine ⟨t, rfl, ht, hfound, ?_⟩
    obtain ⟨_, i, hi, hit, hprevious⟩ := List.find?_eq_some_iff_getElem.mp hs
    have hindex : i = t := by simpa only [List.getElem_range] using hit
    have hprev : ∀ j < t, prefixMass weights j < total / 6 := by
      intro j hj
      have hb := hprevious j (by omega)
      have hn : ¬ total / 6 ≤ prefixMass weights j := by simpa using hb
      exact lt_of_not_ge hn
    by_cases ht0 : t = 0
    · have hsmall0 := hsmall t ht
      rw [ht0] at hsmall0 ⊢
      simp only [prefixMass, Nat.zero_add, Finset.sum_range_one]
      linarith
    · have hstep : prefixMass weights t = prefixMass weights (t - 1) + weights t := by
        unfold prefixMass
        rw [Finset.sum_range_succ, Nat.sub_add_cancel (by omega)]
      rw [hstep]
      have hp := hprev (t - 1) (by omega)
      have hb := hsmall t ht
      linarith

/-- Every returned threshold separates positive mass on both sides and
has product demand at least 5M²/36. -/
theorem demand_bound (total retained : ℚ) (hpos : 0 < total)
    (hlow : total / 6 ≤ retained) (hhigh : retained ≤ (5 / 6 : ℚ) * total) :
    0 < retained ∧ 0 < total - retained ∧ (5 / 36 : ℚ) * total ^ 2 ≤ retained * (total - retained) := by
  refine ⟨by linarith, by linarith, ?_⟩
  have hprod := mul_nonneg (show 0 ≤ retained - total / 6 by linarith)
    (show 0 ≤ (5 / 6 : ℚ) * total - retained by linarith)
  nlinarith

end Lax455465Proofs.BalancedPrefix
