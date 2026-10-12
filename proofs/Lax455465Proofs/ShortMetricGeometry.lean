import Lax455465Proofs.ShortMetricBounds
import Lax455465Proofs.ShortRouteAssembly
import Lax455465Proofs.ShortConnections
import Mathlib.Algebra.Order.Floor.Semiring

open scoped BigOperators
namespace Lax455465Proofs.ShortMetricGeometry
open Lax455465.RationalEncoding BoundedDistances DistanceRoutes RegionRounding UniformCutBounds

set_option maxHeartbeats 1200000 in
/-- Low weighted length cannot separate all pairs even when walks are
restricted to O(q log n) hops, where q is incident capacity divided by
n times the cut lower bound. This is the geometric short-path estimate. -/
theorem cheap_routes {n : ℕ} (I : RationalInstance n) (hw : ∀ v,I.weight v=1)
    (hn : 2 ≤ n) (s q : ℚ) (hs : 0 < s) (hq : 1/2 ≤ q) (hcut : CutLower I s)
    (hrows : ∀ v,(∑ u,(I.capacity v u : ℚ)) ≤ q*n*s)
    (hcols : ∀ v,(∑ u,(I.capacity u v : ℚ)) ≤ q*n*s)
    (ell : Length n) (hell : ∀ u v,0 ≤ ell u v) (hdiag : ∀ v,ell v v=0)
    (hsym : ∀ u v,ell u v=ell v u)
    (hcost : metricCost I ell ≤ s/(1024*(RegionBudget.steps n : ℚ)))
    (L : ℕ) (hL : 1024*(RegionBudget.steps n : ℚ)*q ≤ L) :
    ∃ a : Fin n → ℚ, (∀ v,0 ≤ a v) ∧
      (∑ v,a v) ≤ 1/(128*(RegionBudget.steps n : ℚ)*n) ∧
      ∀ u v,∃ k ≤ L,∃ c ≤ a u+a v+1/(2*(n : ℚ)^2),Route ell u v k c := by
  let K := RegionBudget.steps n
  let W : ℚ := s/(1024*K)
  let R : ℚ := q*n*s
  let delta : ℚ := 1/(1024*K*q*(n : ℚ)^2)
  let radius : ℚ := 1/(4*(n : ℚ)^2)
  let D : Length n := RationalDistances.solve (regularized ell delta)
  have hnq : (0 : ℚ) < n := by exact_mod_cast (show 0 < n by omega)
  have hK : (0 : ℚ) < K := by exact_mod_cast RegionBudget.steps_pos n
  have hq0 : 0 < q := by linarith
  have hW : 0 < W := by dsimp [W]; positivity
  have hR : 0 < R := by dsimp [R]; positivity
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  have hrad : 0 < radius := by dsimp [radius]; positivity
  have hd := RationalDistances.nonnegative_iterate (regularized ell delta) (List.finRange n)
    (regularized_nonnegative ell delta hell hdelta.le)
  have hdDiag := RationalDistances.diagonal_iterate (regularized ell delta) (List.finRange n)
    (regularized_nonnegative ell delta hell hdelta.le) (regularized_diagonal ell delta)
  have hdTri := RationalDistances.triangle (regularized ell delta)
    (regularized_nonnegative ell delta hell hdelta.le)
  have hreg := ShortMetricBounds.regularized_cost I ell delta R hdelta.le hrows
  have hmul : delta*n*R=W := by
    dsimp [delta,R,W]
    field_simp
    <;> ring
  rw [hmul] at hreg
  have hdCost : metricCost I D ≤ 2*W := by
    have hle := (ShortMetricBounds.solve_cost I (regularized ell delta)).trans hreg
    change metricCost I ell ≤ W at hcost
    linarith
  have hdPos : 0 < metricCost I D := ShortMetricBounds.regularized_cost_pos I hw hn s hs hcut ell hell delta hdelta
  have hp := ShortMetricBounds.support_eq I hw
  have htotal := uniform_total I hw
  have hcheap : (288/5 : ℚ)*(RegionBudget.steps (supportSize I) : ℚ)*metricCost I D < s := by
    rw [hp]
    have hKW : (K : ℚ)*W=s/1024 := by dsimp [W]; field_simp
    have hm := mul_le_mul_of_nonneg_left hdCost hK.le
    change (288/5 : ℚ)*(K : ℚ)*metricCost I D < s
    nlinarith
  obtain ⟨ball,hball⟩ := ShortLargeBall.exists_large I D s hcut (by rw [htotal]; exact hnq)
    (by simpa only [hp] using hn) hd hdDiag hdTri hdPos hcheap
  let T := RegionCharging.ball (D ball.root) ball.radius
  have hT : (2/3 : ℚ)*n ≤ (T.card : ℚ) := by
    have ht := hball.2.2.1
    rw [htotal,uniform_mass I hw] at ht
    exact ht
  have hballRadius : ∀ t∈T,D ball.root t ≤ radius := by
    intro t ht
    have hh : D ball.root t < ball.radius := (Finset.mem_filter.mp ht).2
    have hh' := hball.2.1
    change ball.radius ≤ 1/(4*LargeBallRounding.total I^2) at hh'
    rw [htotal] at hh'
    exact hh.le.trans hh'
  let d : ℚ := 1/(4*q)
  let E : ℚ := 1/(256*K*n)
  let m : ℕ := ⌈4*q⌉₊
  have hd0 : 0 < d := by dsimp [d]; positivity
  have hd1 : d ≤ 1 := by
    dsimp [d]
    apply (div_le_iff₀ (by positivity : (0 : ℚ) < 4*q)).mpr
    linarith
  have hE : 0 < E := by dsimp [E]; positivity
  have hdR : d*R=(n : ℚ)*s/4 := by dsimp [d,R]; field_simp
  have hT' : d*R ≤ s*(T.card : ℚ) := by rw [hdR]; nlinarith
  have hdRE : d*R*E=W := by
    dsimp [d,R,E,W]
    field_simp
    <;> ring
  have hcost' : metricCost I ell ≤ d*R*E := by rw [hdRE]; exact hcost
  have hm : 1 ≤ (m : ℚ)*d := by
    have hceil : 4*q ≤ (m : ℚ) := Nat.le_ceil _
    have he : (4*q)*d=1 := by dsimp [d]; field_simp
    nlinarith [mul_le_mul_of_nonneg_right hceil hd0.le]
  have hmUpper : (m : ℚ) ≤ 6*q := by
    have hceil : (m : ℚ) < 4*q+1 := Nat.ceil_lt_add_one (by positivity)
    linarith
  obtain ⟨havg,hconnect⟩ := ShortConnections.connections I hw s R d E hs.le hR hd0.le hd1 hE hcut hcols
    T hT' ell hell hcost' m K hm (ShortConnections.budget_decay n (by omega))
  let a := run ell T (4*E) (m*K)
  refine ⟨a,nonnegative ell T (4*E) hell (by positivity) (m*K),?_,?_⟩
  · have he : 2*E=1/(128*(K : ℚ)*n) := by dsimp [E]; ring
    simpa only [he,K] using havg
  · have hballRoutes := ShortRouteAssembly.ball_routes ell hell hdiag delta radius hdelta.le T ball.root hballRadius
    have he : 2*radius/delta=512*(K : ℚ)*q := by
      dsimp [radius,delta]
      field_simp
      <;> ring
    have hbudget : 2*((m*K : ℕ) : ℚ)+2*radius/delta ≤ L := by
      rw [he,Nat.cast_mul]
      have hh := mul_le_mul_of_nonneg_right hmUpper hK.le
      have hKq := mul_nonneg hK.le hq0.le
      change 1024*(K : ℚ)*q ≤ L at hL
      nlinarith
    have hh := ShortRouteAssembly.pairs ell hsym T ball.root radius delta hdelta (m*K) L a hbudget hballRoutes hconnect
    have hr : 2*radius=1/(2*(n : ℚ)^2) := by dsimp [radius]; ring
    simpa only [hr] using hh

end Lax455465Proofs.ShortMetricGeometry
