import Lax455465Proofs.DistanceRoutes

namespace Lax455465Proofs.ShortRouteAssembly
open BoundedDistances DistanceRoutes

/-- Combine two short connections with two routes inside a root ball.
All four pieces are actual walks, and their hop counts are added explicitly. -/
theorem pairs {n : ℕ} (ell : Length n) (hsym : ∀ u v,ell u v=ell v u)
    (T : Finset (Fin n)) (root : Fin n) (radius delta : ℚ) (hdelta : 0 < delta)
    (H L : ℕ) (a : Fin n → ℚ)
    (hbudget : 2*(H : ℚ)+2*radius/delta ≤ L)
    (hball : ∀ t∈T,∃ k c,Route ell root t k c ∧ c ≤ radius ∧ delta*k ≤ radius)
    (hconnect : ∀ v,∃ t∈T,∃ h ≤ H,∃ c ≤ a v,Route ell t v h c) :
    ∀ u v,∃ k ≤ L,∃ c ≤ a u+a v+2*radius,Route ell u v k c := by
  intro u v
  obtain ⟨s,hs,hu,hhu,cu,hcu,ru⟩ := hconnect u
  obtain ⟨t,ht,hv,hhv,cv,hcv,rv⟩ := hconnect v
  obtain ⟨ks,cs,rs,hcs,hks⟩ := hball s hs
  obtain ⟨kt,ct,rt,hct,hkt⟩ := hball t ht
  have hsQ : (ks : ℚ) ≤ radius/delta := (le_div_iff₀ hdelta).mpr (by nlinarith)
  have htQ : (kt : ℚ) ≤ radius/delta := (le_div_iff₀ hdelta).mpr (by nlinarith)
  have huQ : (hu : ℚ) ≤ H := by exact_mod_cast hhu
  have hvQ : (hv : ℚ) ≤ H := by exact_mod_cast hhv
  refine ⟨hu+(ks+(kt+hv)),?_,cu+(cs+(ct+cv)),by linarith,
    (ru.reverse hsym).trans ((rs.reverse hsym).trans (rt.trans rv))⟩
  have hbound : ((hu+(ks+(kt+hv)) : ℕ) : ℚ) ≤ L := by
    have he : 2*radius/delta=2*(radius/delta) := by ring
    rw [he] at hbudget
    push_cast
    linarith
  exact_mod_cast hbound

/-- Every member of a regularized metric ball has a route whose number
of genuine edges is at most the radius divided by the regularization. -/
theorem ball_routes {n : ℕ} (ell : Length n) (hell : ∀ u v,0 ≤ ell u v)
    (hdiag : ∀ v,ell v v=0) (delta radius : ℚ) (hdelta : 0 ≤ delta)
    (T : Finset (Fin n)) (root : Fin n)
    (hball : ∀ t∈T,RationalDistances.solve (regularized ell delta) root t ≤ radius) :
    ∀ t∈T,∃ k c,Route ell root t k c ∧ c ≤ radius ∧ delta*k ≤ radius := by
  intro t ht
  obtain ⟨k,c,hc,hr⟩ := solve_routes (regularized ell delta) (regularized_diagonal ell delta) root t
  obtain ⟨c',hc',hr'⟩ := hr.smaller (original_le_regularized ell delta hdiag hdelta)
  have hk := hr.hops_bound delta (regularized_lower ell delta hell)
  exact ⟨k,c',hr',hc'.trans (hc.trans (hball t ht)),hk.trans (hc.trans (hball t ht))⟩

end Lax455465Proofs.ShortRouteAssembly
