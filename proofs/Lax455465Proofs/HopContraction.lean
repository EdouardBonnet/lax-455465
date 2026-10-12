import Lax455465Proofs.UniformCutBounds

open scoped BigOperators
namespace Lax455465Proofs.HopContraction
open Lax455465.RationalEncoding

/-- One shortest-path relaxation controls every violated edge inequality
by the drop at its destination. -/
theorem edge_drop {n : ℕ} (I : RationalInstance n) (ell : Fin n → Fin n → ℚ)
    (hell : ∀ u v,0 ≤ ell u v) (a b : Fin n → ℚ)
    (hdec : ∀ v,b v ≤ a v) (hstep : ∀ u v,b v ≤ a u+ell u v) :
    PotentialLayers.edgeCost I a ≤
      (∑ u,∑ v,(I.capacity u v : ℚ)*ell u v)+
      ∑ v,(∑ u,(I.capacity u v : ℚ))*(a v-b v) := by
  calc
    _ ≤ ∑ u,∑ v,(I.capacity u v : ℚ)*(ell u v+(a v-b v)) := by
      apply Finset.sum_le_sum
      intro u _
      apply Finset.sum_le_sum
      intro v _
      apply mul_le_mul_of_nonneg_left _ (NNRat.coe_nonneg _)
      apply max_le
      · linarith [hstep u v]
      · linarith [hell u v,hdec v]
    _ = _ := by
      simp_rw [mul_add,Finset.sum_add_distrib]
      congr 1
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro v _
      exact (Finset.sum_mul _ _ _).symm

/-- A column-capacity bound turns the edge error into an aggregate drop. -/
theorem energy_drop {n : ℕ} (I : RationalInstance n) (ell : Fin n → Fin n → ℚ)
    (hell : ∀ u v,0 ≤ ell u v) (R : ℚ) (hR : ∀ v,(∑ u,(I.capacity u v : ℚ)) ≤ R)
    (a b : Fin n → ℚ) (hdec : ∀ v,b v ≤ a v) (hstep : ∀ u v,b v ≤ a u+ell u v) :
    PotentialLayers.edgeCost I a ≤
      (∑ u,∑ v,(I.capacity u v : ℚ)*ell u v)+R*((∑ v,a v)-(∑ v,b v)) := by
  apply (edge_drop I ell hell a b hdec hstep).trans
  apply add_le_add le_rfl
  calc
    _ ≤ ∑ v,R*(a v-b v) := Finset.sum_le_sum fun v _ =>
      mul_le_mul_of_nonneg_right (hR v) (sub_nonneg.mpr (hdec v))
    _ = _ := by rw [←Finset.mul_sum,Finset.sum_sub_distrib]

/-- Combined with cut expansion, the total capped distance contracts by
one minus the normalized expansion, up to the weighted edge-length cost. -/
theorem one_step {n : ℕ} (I : RationalInstance n) (hw : ∀ v,I.weight v=1)
    (s R : ℚ) (hs : 0 ≤ s) (hR : 0 < R) (hcut : UniformCutBounds.CutLower I s)
    (hcap : ∀ v,(∑ u,(I.capacity u v : ℚ)) ≤ R) (T : Finset (Fin n))
    (ell : Fin n → Fin n → ℚ) (hell : ∀ u v,0 ≤ ell u v)
    (a b : Fin n → ℚ) (ha : ∀ v,0 ≤ a v) (hzero : ∀ v∈T,a v=0)
    (hdec : ∀ v,b v ≤ a v) (hstep : ∀ u v,b v ≤ a u+ell u v) :
    (∑ v,b v) ≤ (1-s*(T.card : ℚ)/R)*(∑ v,a v)+
      (∑ u,∑ v,(I.capacity u v : ℚ)*ell u v)/R := by
  have hc := UniformCutBounds.large_set_coarea I hw s hs hcut T a ha hzero
  have he := energy_drop I ell hell R hcap a b hdec hstep
  apply (mul_le_mul_iff_left₀ hR).mp
  have heq : R*((1-s*(T.card : ℚ)/R)*(∑ v,a v)+
      (∑ u,∑ v,(I.capacity u v : ℚ)*ell u v)/R) =
      (R-s*(T.card : ℚ))*(∑ v,a v)+(∑ u,∑ v,(I.capacity u v : ℚ)*ell u v) := by
    field_simp
    <;> ring
  nlinarith

/-- Iterating an affine contraction keeps an explicit geometric remainder. -/
theorem iterate_bound (D : ℕ → ℚ) (r E : ℚ) (hr : 0 ≤ r)
    (hstep : ∀ k,D (k+1) ≤ r*D k+(1-r)*E) (k : ℕ) :
    D k ≤ E+r^k*(D 0-E) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hm := mul_le_mul_of_nonneg_left ih hr
    calc
      D (k+1) ≤ r*D k+(1-r)*E := hstep k
      _ ≤ r*(E+r^k*(D 0-E))+(1-r)*E := by linarith
      _ = E+r^(k+1)*(D 0-E) := by rw [pow_succ]; ring

/-- A block of m relaxations halves the geometric error whenever m times
the normalized expansion is at least one. -/
theorem block_half (d : ℚ) (hd0 : 0 ≤ d) (hd1 : d ≤ 1) (m : ℕ) (hm : 1 ≤ m*d) :
    (1-d)^m ≤ 1/2 := by
  have hprod : (1+(m : ℚ)*d)*(1-d)^m ≤ 1 := by
    clear hm
    induction m with
    | zero => simp
    | succ m ih =>
      have hp : 0 ≤ (1-d)^m := pow_nonneg (by linarith) _
      have hmd : 0 ≤ (m : ℚ)*d^2 := mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
      have hh : (1+((m+1 : ℕ) : ℚ)*d)*(1-d) ≤ 1+(m : ℚ)*d := by
        push_cast
        nlinarith
      rw [pow_succ]
      nlinarith [mul_le_mul_of_nonneg_right hh hp]
  have hp : 0 ≤ (1-d)^m := pow_nonneg (by linarith) _
  nlinarith

end Lax455465Proofs.HopContraction
