import Lax455465Proofs.RegionVolume
import Lax455465Proofs.FiniteRegionGrowth

open scoped BigOperators

namespace Lax455465Proofs.RegionInterval

open RegionVolume

/-- Exact product of the two seeded ball volumes. -/
def productVolume {n : ℕ} (capacity length : Matrix n)
    (outDistance inDistance : Fin n → ℚ) (seed radius : ℚ) : ℚ :=
  volume capacity length outDistance seed radius *
    volume (fun u v => capacity v u) (fun u v => length v u) inDistance seed radius

private theorem transpose_weight {n : ℕ} (capacity length : Matrix n) :
    weight (fun u v => capacity v u) (fun u v => length v u) = weight capacity length := by
  unfold weight
  rw [Finset.sum_comm]

/-- Product-volume budget for every candidate radius. -/
theorem budget {n : ℕ} (capacity length : Matrix n)
    (outDistance inDistance : Fin n → ℚ) (seed radius : ℚ)
    (hc : ∀ u v, 0 ≤ capacity u v) (hl : ∀ u v, 0 ≤ length u v)
    (hseed : 0 ≤ seed) :
    seed ^ 2 ≤ productVolume capacity length outDistance inDistance seed radius ∧
    productVolume capacity length outDistance inDistance seed radius ≤
      (seed + weight capacity length) ^ 2 := by
  obtain ⟨houtLo, houtHi⟩ := bounds capacity length outDistance seed radius hc hl
  obtain ⟨hinLo, hinHi⟩ := bounds (fun u v => capacity v u)
    (fun u v => length v u) inDistance seed radius (fun u v => hc v u) (fun u v => hl v u)
  rw [transpose_weight] at hinHi
  unfold productVolume
  constructor
  · simpa only [pow_two] using mul_le_mul houtLo hinLo hseed (hseed.trans houtLo)
  · simpa only [pow_two] using mul_le_mul houtHi hinHi
      (hseed.trans hinLo) (hseed.trans houtLo |>.trans houtHi)

/-- With seed W/p, the whole search has product-volume budget 4p² seed².
The same bound holds in every residual graph whose length cost is at most W. -/
theorem normalized_budget {n : ℕ} (capacity length : Matrix n)
    (outDistance inDistance : Fin n → ℚ) (seed radius p : ℚ)
    (hc : ∀ u v, 0 ≤ capacity u v) (hl : ∀ u v, 0 ≤ length u v)
    (hseed : 0 ≤ seed) (hp : 1 ≤ p) (hweight : weight capacity length ≤ p * seed) :
    productVolume capacity length outDistance inDistance seed radius ≤ 4 * p ^ 2 * seed ^ 2 := by
  have hweightNN : 0 ≤ weight capacity length := by
    exact Finset.sum_nonneg (fun u _ => Finset.sum_nonneg (fun v _ =>
      mul_nonneg (hc u v) (hl u v)))
  have hseedLe : seed ≤ p * seed := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hp hseed
  have htotal : seed + weight capacity length ≤ 2 * p * seed := by linarith
  have hsq := mul_self_le_mul_self (add_nonneg hseed hweightNN) htotal
  calc
    productVolume capacity length outDistance inDistance seed radius ≤
        (seed + weight capacity length) ^ 2 := (budget _ _ _ _ _ _ hc hl hseed).2
    _ ≤ (2 * p * seed) ^ 2 := by simpa only [pow_two] using hsq
    _ = 4 * p ^ 2 * seed ^ 2 := by ring

/-- Both volumes, and therefore their nonnegative product, are monotone. -/
theorem monotone {n : ℕ} (capacity length : Matrix n)
    (outDistance inDistance : Fin n → ℚ) (seed a b : ℚ)
    (hc : ∀ u v, 0 ≤ capacity u v) (hl : ∀ u v, 0 ≤ length u v)
    (hseed : 0 ≤ seed) (hab : a ≤ b) :
    productVolume capacity length outDistance inDistance seed a ≤
      productVolume capacity length outDistance inDistance seed b := by
  have hout := RegionVolume.monotone capacity length outDistance seed a b hc hab
  have hin := RegionVolume.monotone (fun u v => capacity v u) (fun u v => length v u)
    inDistance seed a b (fun u v => hc v u) hab
  have hinLo := (bounds (fun u v => capacity v u) (fun u v => length v u)
    inDistance seed a (fun u v => hc v u) (fun u v => hl v u)).1
  have houtLo := (bounds capacity length outDistance seed b hc hl).1
  exact mul_le_mul hout hin (hseed.trans hinLo) (hseed.trans houtLo)

/-- If the chosen outward or inward boundary exceeds the tested bound, the
product volume gains at least width × slope × its initial value. -/
theorem gain {n : ℕ} (capacity length : Matrix n)
    (outDistance inDistance : Fin n → ℚ) (seed a b beta : ℚ)
    (hc : ∀ u v, 0 ≤ capacity u v) (hl : ∀ u v, 0 ≤ length u v)
    (hseed : 0 ≤ seed) (hab : a ≤ b) (hbeta : 0 ≤ beta)
    (houtEvent : NoEvent outDistance a b) (hinEvent : NoEvent inDistance a b)
    (houtLip : ∀ u v, outDistance v - outDistance u ≤ length u v)
    (hinLip : ∀ u v, inDistance v - inDistance u ≤ length v u)
    (hbad : beta * volume capacity length outDistance seed b ≤
        boundary capacity outDistance b ∨
      beta * volume (fun u v => capacity v u) (fun u v => length v u)
        inDistance seed b ≤ boundary (fun u v => capacity v u) inDistance b) :
    (b - a) * beta * productVolume capacity length outDistance inDistance seed a ≤
      productVolume capacity length outDistance inDistance seed b -
        productVolume capacity length outDistance inDistance seed a := by
  have houtLo := (bounds capacity length outDistance seed a hc hl).1
  have hinLo := (bounds (fun u v => capacity v u) (fun u v => length v u)
    inDistance seed a (fun u v => hc v u) (fun u v => hl v u)).1
  have houtMono := RegionVolume.monotone capacity length outDistance seed a b hc hab
  have hinMono := RegionVolume.monotone (fun u v => capacity v u) (fun u v => length v u)
    inDistance seed a b (fun u v => hc v u) hab
  unfold productVolume
  rcases hbad with houtBad | hinBad
  · exact FiniteRegionGrowth.product_gain_left _ _ _ _ _ _ _
      (hseed.trans houtLo) (hseed.trans hinLo) houtMono hinMono
      (sub_nonneg.mpr hab) hbeta houtBad
      (RegionVolume.gain capacity length outDistance seed a b hc hab houtEvent houtLip)
  · exact FiniteRegionGrowth.product_gain_right _ _ _ _ _ _ _
      (hseed.trans houtLo) (hseed.trans hinLo) houtMono hinMono
      (sub_nonneg.mpr hab) hbeta hinBad
      (RegionVolume.gain (fun u v => capacity v u) (fun u v => length v u)
        inDistance seed a b (fun u v => hc v u) hab hinEvent hinLip)

end Lax455465Proofs.RegionInterval
