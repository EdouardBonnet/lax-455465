import Lax455465Proofs.BoundedDistances
import Lax455465Proofs.RationalDistances

namespace Lax455465Proofs.DistanceRoutes
open BoundedDistances RationalDistances

theorem endpoints_of_zero {n : ℕ} {ell : Length n} {u v : Fin n} {k : ℕ} {c : ℚ}
    (h : Route ell u v k c) : k=0 → u=v := by
  induction h with
  | refl => intro; rfl
  | edge => intro hk; omega
  | trans _ _ ih1 ih2 => intro hk; exact (ih1 (by omega)).trans (ih2 (by omega))

/-- Floyd–Warshall retains genuine routes, including through repeated pivots. -/
theorem iterate_routes {n : ℕ} (ell d : Length n) (pivots : List (Fin n))
    (hroute : ∀ u v,∃ k c,c ≤ d u v ∧ Route ell u v k c) :
    ∀ u v,∃ k c,c ≤ iterate d pivots u v ∧ Route ell u v k c := by
  induction pivots generalizing d with
  | nil => exact hroute
  | cons p ps ih =>
    apply ih (RationalDistances.step d p)
    intro u v
    by_cases hc : d u v ≤ d u p+d p v
    · simpa only [RationalDistances.step,min_eq_left hc] using hroute u v
    · obtain ⟨a,x,hx,rx⟩ := hroute u p
      obtain ⟨b,y,hy,ry⟩ := hroute p v
      exact ⟨a+b,x+y,by dsimp [RationalDistances.step]; rw [min_eq_right (le_of_not_ge hc)]; linarith,rx.trans ry⟩

theorem solve_routes {n : ℕ} (ell : Length n) (hdiag : ∀ u,ell u u=0) (u v : Fin n) :
    ∃ k c,c ≤ solve ell u v ∧ Route ell u v k c := by
  apply iterate_routes ell ell (List.finRange n) _ u v
  intro s t
  by_cases he : s=t
  · subst t; exact ⟨0,0,by rw [hdiag],.refl s⟩
  · exact ⟨1,ell s t,le_rfl,.edge he⟩

theorem solve_offdiag_lower {n : ℕ} (ell : Length n) (hdiag : ∀ u,ell u u=0)
    (delta : ℚ) (hdelta : 0 ≤ delta) (hmin : ∀ u v,u ≠ v → delta ≤ ell u v)
    (u v : Fin n) (hne : u ≠ v) : delta ≤ solve ell u v := by
  obtain ⟨k,c,hc,hr⟩ := solve_routes ell hdiag u v
  have hk : 0 < k := by by_contra hn; exact hne (endpoints_of_zero hr (by omega))
  have hkq : (1 : ℚ) ≤ k := by exact_mod_cast hk
  have hm := hr.hops_bound delta hmin
  nlinarith

theorem step_symmetric {n : ℕ} (d : Length n) (hsym : ∀ u v,d u v=d v u) (p : Fin n) :
    ∀ u v,RationalDistances.step d p u v=RationalDistances.step d p v u := by
  intro u v
  simp only [RationalDistances.step]
  rw [hsym u v,hsym u p,hsym p v,add_comm (d p u)]

theorem iterate_symmetric {n : ℕ} (d : Length n) (hsym : ∀ u v,d u v=d v u)
    (ps : List (Fin n)) : ∀ u v,iterate d ps u v=iterate d ps v u := by
  induction ps generalizing d with
  | nil => exact hsym
  | cons p ps ih => exact ih _ (step_symmetric d hsym p)

/-- Each genuine edge receives a positive hop penalty; the diagonal stays
zero, so stationary segments are free. -/
def regularized {n : ℕ} (ell : Length n) (delta : ℚ) : Length n :=
  fun u v => if u=v then 0 else ell u v+delta

theorem regularized_nonnegative {n : ℕ} (ell : Length n) (delta : ℚ)
    (hell : ∀ u v,0 ≤ ell u v) (hdelta : 0 ≤ delta) : Nonnegative (regularized ell delta) := by
  intro u v; dsimp [regularized]; split_ifs <;> linarith [hell u v]

@[simp] theorem regularized_diagonal {n : ℕ} (ell : Length n) (delta : ℚ) (v : Fin n) :
    regularized ell delta v v=0 := by simp [regularized]

theorem regularized_lower {n : ℕ} (ell : Length n) (delta : ℚ)
    (hell : ∀ u v,0 ≤ ell u v) (u v : Fin n) (hne : u ≠ v) :
    delta ≤ regularized ell delta u v := by simp only [regularized,if_neg hne]; linarith [hell u v]

theorem original_le_regularized {n : ℕ} (ell : Length n) (delta : ℚ)
    (hdiag : ∀ u,ell u u=0) (hdelta : 0 ≤ delta) : ∀ u v,ell u v ≤ regularized ell delta u v := by
  intro u v; dsimp [regularized]
  split_ifs with he
  · subst v; rw [hdiag]
  · linarith

end Lax455465Proofs.DistanceRoutes
