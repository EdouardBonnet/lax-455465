import Lax455465Proofs.ShortLargeBall
import Lax455465Proofs.DistanceRoutes

open scoped BigOperators
namespace Lax455465Proofs.ShortMetricBounds
open Lax455465.RationalEncoding BoundedDistances DistanceRoutes RationalDistances RegionRounding

/-- Uniform instances have precisely n demand-support vertices. -/
theorem support_eq {n : ℕ} (I : RationalInstance n) (hw : ∀ v,I.weight v=1) : supportSize I=n := by
  simp [supportSize,RegionSelection.support,RegionLoop.weights,hw]

theorem regularized_cost {n : ℕ} (I : RationalInstance n) (ell : Length n) (delta R : ℚ)
    (hdelta : 0 ≤ delta) (hrows : ∀ v,(∑ u,(I.capacity v u : ℚ)) ≤ R) :
    metricCost I (regularized ell delta) ≤ metricCost I ell+delta*(n : ℚ)*R := by
  have hterm (u v : Fin n) :
      (I.capacity u v : ℚ)*regularized ell delta u v ≤ (I.capacity u v : ℚ)*(ell u v+delta) := by
    by_cases he : u=v
    · subst v; simp [I.loopless]
    · simp [regularized,he]
  have hsum := Finset.sum_le_sum fun u (_ : u∈(Finset.univ : Finset (Fin n))) =>
    Finset.sum_le_sum fun v (_ : v∈(Finset.univ : Finset (Fin n))) => hterm u v
  have htotal : (∑ u,∑ v,(I.capacity u v : ℚ)) ≤ n*R := by
    calc
      _ ≤ ∑ _u : Fin n,R := Finset.sum_le_sum fun u _ => hrows u
      _ = _ := by simp
  change (∑ u,∑ v,(I.capacity u v : ℚ)*regularized ell delta u v) ≤
    (∑ u,∑ v,(I.capacity u v : ℚ)*ell u v)+delta*n*R
  calc
    _ ≤ ∑ u,∑ v,(I.capacity u v : ℚ)*(ell u v+delta) := hsum
    _ = (∑ u,∑ v,(I.capacity u v : ℚ)*ell u v)+delta*(∑ u,∑ v,(I.capacity u v : ℚ)) := by
      simp_rw [mul_add,Finset.sum_add_distrib,←Finset.sum_mul]
      ring
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left htotal hdelta]

theorem solve_cost {n : ℕ} (I : RationalInstance n) (ell : Length n) :
    metricCost I (solve ell) ≤ metricCost I ell := by
  exact Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ =>
    mul_le_mul_of_nonneg_left (iterate_le ell (List.finRange n) u v) (NNRat.coe_nonneg _)

/-- Regularization makes the metric cost positive when cut expansion is
positive, even if all original dual edge lengths vanish. -/
theorem regularized_cost_pos {n : ℕ} (I : RationalInstance n) (hw : ∀ v,I.weight v=1)
    (hn : 2 ≤ n) (s : ℚ) (hs : 0 < s) (hcut : UniformCutBounds.CutLower I s)
    (ell : Length n) (hell : ∀ u v,0 ≤ ell u v) (delta : ℚ) (hdelta : 0 < delta) :
    0 < metricCost I (solve (regularized ell delta)) := by
  obtain ⟨u,v,hne,hcap⟩ := UniformCutBounds.positive_edge I hw hn s hs hcut
  have hbound := solve_offdiag_lower (regularized ell delta) (regularized_diagonal ell delta)
    delta hdelta.le (regularized_lower ell delta hell) u v hne
  have hd := nonnegative_iterate (regularized ell delta) (List.finRange n)
    (regularized_nonnegative ell delta hell hdelta.le)
  have hp : 0 < (I.capacity u v : ℚ)*solve (regularized ell delta) u v :=
    mul_pos hcap (hdelta.trans_le hbound)
  have hi := Finset.single_le_sum
    (fun w (_ : w∈(Finset.univ : Finset (Fin n))) => mul_nonneg (NNRat.coe_nonneg (I.capacity u w)) (hd u w))
    (Finset.mem_univ v)
  have ho := Finset.single_le_sum
    (fun x (_ : x∈(Finset.univ : Finset (Fin n))) => Finset.sum_nonneg
      (fun y (_ : y∈(Finset.univ : Finset (Fin n))) => mul_nonneg (NNRat.coe_nonneg (I.capacity x y)) (hd x y))) (Finset.mem_univ u)
  exact hp.trans_le (hi.trans ho)

end Lax455465Proofs.ShortMetricBounds
