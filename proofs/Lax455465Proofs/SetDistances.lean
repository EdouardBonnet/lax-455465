import Lax455465Proofs.RationalDistances
import Mathlib.Data.Finset.Lattice.Fold

set_option backward.isDefEq.respectTransparency false

namespace Lax455465Proofs.SetDistances

open RationalDistances

def fromSet {n : ℕ} (d : Distance n) (S : Finset (Fin n)) (hS : S.Nonempty) (v : Fin n) : ℚ :=
  S.inf' hS fun u => d u v

def toSet {n : ℕ} (d : Distance n) (S : Finset (Fin n)) (hS : S.Nonempty) (v : Fin n) : ℚ :=
  S.inf' hS fun u => d v u

theorem from_nonnegative {n : ℕ} (d : Distance n) (S : Finset (Fin n)) (hS : S.Nonempty)
    (hd : Nonnegative d) (v : Fin n) : 0 ≤ fromSet d S hS v :=
  Finset.le_inf' hS _ fun u _ => hd u v

theorem to_nonnegative {n : ℕ} (d : Distance n) (S : Finset (Fin n)) (hS : S.Nonempty)
    (hd : Nonnegative d) (v : Fin n) : 0 ≤ toSet d S hS v :=
  Finset.le_inf' hS _ fun u _ => hd v u

theorem from_zero {n : ℕ} (d : Distance n) (S : Finset (Fin n)) (hS : S.Nonempty)
    (hd : Nonnegative d) (hdiag : ∀ v, d v v = 0) (v : Fin n) (hv : v ∈ S) :
    fromSet d S hS v = 0 := by
  apply le_antisymm _ (from_nonnegative d S hS hd v)
  have h := Finset.inf'_le (fun u => d u v) hv
  simpa only [hdiag, fromSet] using h

theorem to_zero {n : ℕ} (d : Distance n) (S : Finset (Fin n)) (hS : S.Nonempty)
    (hd : Nonnegative d) (hdiag : ∀ v, d v v = 0) (v : Fin n) (hv : v ∈ S) :
    toSet d S hS v = 0 := by
  apply le_antisymm _ (to_nonnegative d S hS hd v)
  have h := Finset.inf'_le (fun u => d v u) hv
  simpa only [hdiag, toSet] using h

/-- Distance from a nonempty set is a directed Lipschitz potential. -/
theorem from_lipschitz {n : ℕ} (d : Distance n) (S : Finset (Fin n)) (hS : S.Nonempty)
    (htri : ∀ u v w, d u w ≤ d u v + d v w) (u v : Fin n) :
    fromSet d S hS v - fromSet d S hS u ≤ d u v := by
  obtain ⟨s, hs, hmin⟩ := Finset.exists_mem_eq_inf' hS (fun t => d t u)
  change fromSet d S hS u = d s u at hmin
  have hbound := Finset.inf'_le (fun t => d t v) hs
  change fromSet d S hS v ≤ d s v at hbound
  linarith [htri s u v]

/-- The negative distance to a set has the same directed Lipschitz orientation. -/
theorem negative_to_lipschitz {n : ℕ} (d : Distance n) (S : Finset (Fin n)) (hS : S.Nonempty)
    (htri : ∀ u v w, d u w ≤ d u v + d v w) (u v : Fin n) :
    -toSet d S hS v - -toSet d S hS u ≤ d u v := by
  obtain ⟨s, hs, hmin⟩ := Finset.exists_mem_eq_inf' hS (fun t => d v t)
  change toSet d S hS v = d v s at hmin
  have hbound := Finset.inf'_le (fun t => d u t) hs
  change toSet d S hS u ≤ d u s at hbound
  linarith [htri u v s]

/-- Two root balls control all pair distances by distances to and from those balls. -/
theorem root_balls_bound {n : ℕ} (d : Distance n) (Tin Tout : Finset (Fin n))
    (hin : Tin.Nonempty) (hout : Tout.Nonempty) (root : Fin n) (radius : ℚ)
    (htri : ∀ u v w, d u w ≤ d u v + d v w)
    (hinRadius : ∀ s ∈ Tin, d s root ≤ radius)
    (houtRadius : ∀ t ∈ Tout, d root t ≤ radius) (u v : Fin n) :
    d u v ≤ toSet d Tin hin u + 2 * radius + fromSet d Tout hout v := by
  obtain ⟨s, hs, hminIn⟩ := Finset.exists_mem_eq_inf' hin (fun t => d u t)
  obtain ⟨t, ht, hminOut⟩ := Finset.exists_mem_eq_inf' hout (fun t => d t v)
  change toSet d Tin hin u = d u s at hminIn
  change fromSet d Tout hout v = d t v at hminOut
  linarith [htri u s v, htri s root v, htri root t v,
    hinRadius s hs, houtRadius t ht]

end Lax455465Proofs.SetDistances
