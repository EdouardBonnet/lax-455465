import Lax455465Proofs.BoundedDistances

namespace Lax455465Proofs.LayeredRouteBounds
open BoundedDistances

/-- Layer-indexed potentials telescope along an actual walk. -/
theorem route_bound {n : ℕ} (ell : Length n) (p : ℕ → Fin n → ℚ) (L : ℕ)
    (hstep : ∀ j,j < L → ∀ u v,p (j+1) v-p j u ≤ ell u v)
    {s t : Fin n} {k : ℕ} {c : ℚ} (hr : Route ell s t k c) :
    ∀ j,j+k ≤ L → p (j+k) t-p j s ≤ c := by
  induction hr with
  | refl v => intro j hj; simp
  | @edge u v hne => intro j hj; exact hstep j (by omega) u v
  | @trans u v w a b x y r1 r2 ih1 ih2 =>
    intro j hj
    have h1 := ih1 j (by omega)
    have h2 := ih2 (j+a) (by omega)
    rw [Nat.add_assoc] at h2
    linarith

/-- Waiting at the endpoint pads a shorter walk to the full LP budget. -/
theorem wait_bound {n : ℕ} (ell : Length n) (hdiag : ∀ v,ell v v=0)
    (p : ℕ → Fin n → ℚ) (L : ℕ)
    (hstep : ∀ j,j < L → ∀ u v,p (j+1) v-p j u ≤ ell u v)
    (v : Fin n) (j k : ℕ) (hjk : j ≤ k) (hk : k ≤ L) : p k v ≤ p j v := by
  induction k with
  | zero =>
    have hj : j=0 := by omega
    subst j
    rfl
  | succ k ih =>
    by_cases hj : j ≤ k
    · have hh := hstep k (by omega) v v
      rw [hdiag] at hh
      exact (by linarith : p (k+1) v ≤ p k v).trans (ih hj (by omega))
    · have he : j=k+1 := by omega
      subst j
      rfl

theorem padded_route_bound {n : ℕ} (ell : Length n) (hdiag : ∀ v,ell v v=0)
    (p : ℕ → Fin n → ℚ) (L : ℕ)
    (hstep : ∀ j,j < L → ∀ u v,p (j+1) v-p j u ≤ ell u v)
    {s t : Fin n} {k : ℕ} {c : ℚ} (hr : Route ell s t k c) (hk : k ≤ L) :
    p L t-p 0 s ≤ c := by
  have h1 := route_bound ell p L hstep hr 0 (by omega)
  have h2 := wait_bound ell hdiag p L hstep t k L hk le_rfl
  simp only [Nat.zero_add] at h1
  linarith

end Lax455465Proofs.LayeredRouteBounds
