import Lax455465Proofs.RoundingConstants

namespace Lax455465Proofs.RoundingConstantHeight
open LpInputSize RoundingConstants
open scoped NNRat

structure Bounds (cost total : ℚ≥0) (p M : ℕ) : Prop where
  costBound : Height M (cost : ℚ)
  totalBound : Height M (total : ℚ)
  supportBound : Height M ((p : ℚ≥0) : ℚ)
  stepsBound : Height M ((RegionBudget.steps p : ℚ≥0) : ℚ)
  fourBound : Height M ((4 : ℚ≥0) : ℚ)
  seedBound : Height M (seed cost p : ℚ)
  squareBound : Height M ((total*total : ℚ≥0) : ℚ)
  denominatorBound : Height M ((4*(total*total) : ℚ≥0) : ℚ)
  deltaBound : Height M (delta total : ℚ)
  betaBound : Height M (beta total p : ℚ)
  stepBound : Height M (gridStep total p : ℚ)

/-- A common input height gives a polynomial common height for every
constant used by region growth, including reciprocal intermediates. -/
theorem bounds (cost total : ℚ≥0) (p M : ℕ) (hM : 4≤M)
    (hc : Height M (cost : ℚ)) (ht : Height M (total : ℚ))
    (hp : p≤M) (hk : RegionBudget.steps p≤M) : Bounds cost total p (4*M^3) := by
  have hM1 : 1≤M := by omega
  have hN : M≤4*M^3 := by nlinarith [Nat.le_mul_of_pos_right M (by positivity : 0<M*M)]
  have hNN : M*M≤4*M^3 := by nlinarith [Nat.le_mul_of_pos_right (M*M) (by omega : 0<M)]
  have hfourSq : 4*(M*M)≤4*M^3 := by nlinarith [Nat.le_mul_of_pos_right (M*M) (by omega : 0<M)]
  have natHeight (k : ℕ) (h : k≤M) : Height M ((k : ℚ≥0) : ℚ) := by
    simp only [Height,NNRat.coe_natCast,Rat.num_natCast,Rat.den_natCast,Int.natAbs_natCast]
    exact ⟨h,hM1⟩
  have hpn := natHeight p hp
  have hkn := natHeight (RegionBudget.steps p) hk
  have hf : Height 4 ((4 : ℚ≥0) : ℚ) := by norm_num [Height]
  have hsq : Height (M*M) ((total*total : ℚ≥0) : ℚ) := by simpa only [NNRat.coe_mul] using height_mul ht ht
  have hden : Height (4*(M*M)) ((4*(total*total) : ℚ≥0) : ℚ) := by simpa only [NNRat.coe_mul] using height_mul hf hsq
  have hdelta : Height (4*(M*M)) (delta total : ℚ) := by
    have hh := inverse_height (by nlinarith : 1≤4*(M*M)) hden
    simpa only [delta,pow_two] using hh
  have hs : Height (M*M) (seed cost p : ℚ) := by
    simpa only [seed,div_eq_mul_inv,NNRat.coe_mul] using height_mul hc (inverse_height hM1 hpn)
  have hb : Height (M*(4*(M*M))) (beta total p : ℚ) := by
    simpa only [beta,delta,pow_two,div_eq_mul_inv,inv_inv,NNRat.coe_mul] using height_mul hkn hden
  have hg : Height ((4*(M*M))*M) (gridStep total p : ℚ) := by
    simpa only [gridStep,div_eq_mul_inv,NNRat.coe_mul] using height_mul hdelta (inverse_height hM1 hkn)
  exact ⟨height_mono hc hN,height_mono ht hN,height_mono hpn hN,height_mono hkn hN,
    height_mono hf (by nlinarith),height_mono hs hNN,height_mono hsq hNN,height_mono hden hfourSq,
    height_mono hdelta hfourSq,height_mono hb (by ring_nf; rfl),height_mono hg (by ring_nf; rfl)⟩

end Lax455465Proofs.RoundingConstantHeight
