import Lax455465Proofs.RegionInterval
import Lax455465Proofs.RegionThresholds

namespace Lax455465Proofs.RegionCell

open RegionVolume RegionInterval

/-- Failure at every positive event threshold in a grid cell forces its
product volume to double. All intermediate radii are the actual finite
rational candidate list, not an existential discretization. -/
theorem doubles {n : ℕ} (capacity length : Matrix n)
    (outDistance inDistance : Fin n → ℚ) (seed a b beta : ℚ)
    (hc : ∀ u v, 0 ≤ capacity u v) (hl : ∀ u v, 0 ≤ length u v)
    (hseed : 0 ≤ seed) (ha : 0 ≤ a) (hab : a ≤ b) (hbeta : 0 ≤ beta)
    (houtLip : ∀ u v, outDistance v - outDistance u ≤ length u v)
    (hinLip : ∀ u v, inDistance v - inDistance u ≤ length v u)
    (hbad : ∀ r ∈ RegionThresholds.events outDistance inDistance a b, 0 < r →
      beta * volume capacity length outDistance seed r ≤ boundary capacity outDistance r ∨
      beta * volume (fun u v => capacity v u) (fun u v => length v u) inDistance seed r ≤
        boundary (fun u v => capacity v u) inDistance r)
    (hcell : 1 ≤ (b - a) * beta) :
    2 * productVolume capacity length outDistance inDistance seed a ≤
      productVolume capacity length outDistance inDistance seed b := by
  let radii := RegionThresholds.radius outDistance inDistance a b
  let candidates := RegionThresholds.candidates outDistance inDistance a b
  let k := candidates.length - 1
  let values := fun i => productVolume capacity length outDistance inDistance seed (radii i)
  have hpos : 0 < candidates.length := RegionThresholds.length_pos outDistance inDistance a b
  have hindex : ∀ i < k, i + 1 < candidates.length := by
    intro i hi
    dsimp [k] at hi
    omega
  have hfirst : radii 0 = a := RegionThresholds.radius_first outDistance inDistance a b hab
  have hlast : radii k = b := RegionThresholds.radius_last outDistance inDistance a b hab
  have hwidth : ∀ i < k, radii i ≤ radii (i + 1) := by
    intro i hi
    exact RegionThresholds.radius_monotone outDistance inDistance a b i (hindex i hi)
  have hbase : ∀ i < k, values 0 ≤ values i := by
    intro i hi
    have hii : i < candidates.length := by have h := hindex i hi; omega
    have haRi : a ≤ radii i := by
      dsimp only [radii]
      rw [RegionThresholds.radius_eq_get outDistance inDistance a b ⟨i, hii⟩]
      exact (RegionThresholds.bounds outDistance inDistance a b hab _
        ((Finset.mem_sort (· ≤ ·)).mp (List.get_mem _ ⟨i, hii⟩))).1
    dsimp [values]
    rw [hfirst]
    exact RegionInterval.monotone capacity length outDistance inDistance seed a _ hc hl hseed haRi
  have hgain : ∀ i < k,
      (radii (i + 1) - radii i) * beta * values i ≤ values (i + 1) - values i := by
    intro i hi
    have hinext := hindex i hi
    have hii : i < candidates.length := by omega
    have houtIn := RegionThresholds.no_event outDistance inDistance a b hab i hinext
    have houtEvent : NoEvent outDistance (radii i) (radii (i + 1)) := by
      dsimp only [radii]
      rw [RegionThresholds.radius_eq_get outDistance inDistance a b ⟨i, hii⟩,
        RegionThresholds.radius_eq_get outDistance inDistance a b ⟨i + 1, hinext⟩]
      exact houtIn.1
    have hinEvent : NoEvent inDistance (radii i) (radii (i + 1)) := by
      dsimp only [radii]
      rw [RegionThresholds.radius_eq_get outDistance inDistance a b ⟨i, hii⟩,
        RegionThresholds.radius_eq_get outDistance inDistance a b ⟨i + 1, hinext⟩]
      exact houtIn.2
    have hmem : radii (i + 1) ∈ RegionThresholds.events outDistance inDistance a b := by
      dsimp only [radii]
      rw [RegionThresholds.radius_eq_get outDistance inDistance a b ⟨i + 1, hinext⟩]
      exact (Finset.mem_sort (· ≤ ·)).mp (List.get_mem _ _)
    have hpositive : 0 < radii (i + 1) := by
      have hstrict := (Finset.sortedLT_sort (RegionThresholds.events outDistance inDistance a b))
        (show (⟨0, hpos⟩ : Fin _) < ⟨i + 1, hinext⟩ by change 0 < i + 1; omega)
      have hr0 := RegionThresholds.radius_eq_get outDistance inDistance a b ⟨0, hpos⟩
      have hr1 := RegionThresholds.radius_eq_get outDistance inDistance a b ⟨i + 1, hinext⟩
      have haR : a < radii (i + 1) := by
        calc
          a = radii 0 := hfirst.symm
          _ = (RegionThresholds.candidates outDistance inDistance a b).get ⟨0, hpos⟩ := hr0
          _ < (RegionThresholds.candidates outDistance inDistance a b).get ⟨i + 1, hinext⟩ := hstrict
          _ = radii (i + 1) := hr1.symm
      exact ha.trans_lt haR
    exact RegionInterval.gain capacity length outDistance inDistance seed (radii i) (radii (i + 1))
      beta hc hl hseed (hwidth i hi) hbeta houtEvent hinEvent houtLip hinLip
      (hbad _ hmem hpositive)
  have hvalues : 0 ≤ values 0 := by
    have hlow := (RegionInterval.budget capacity length outDistance inDistance seed (radii 0)
      hc hl hseed).1
    exact (sq_nonneg seed).trans hlow
  have h := FiniteRegionGrowth.doubled_cell values radii beta k hbeta hvalues hwidth hbase hgain
    (by simpa only [hfirst, hlast] using hcell)
  simpa only [values, hfirst, hlast] using h

end Lax455465Proofs.RegionCell
