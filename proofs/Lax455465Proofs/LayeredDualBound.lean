import Lax455465Proofs.LayeredFlowDual
import Lax455465Proofs.LayeredRouteBounds
import Lax455465Proofs.ShortMetricGeometry
import Lax455465Proofs.RouteSimplification

open scoped BigOperators
namespace Lax455465Proofs.LayeredDualBound
open Lax455465.RationalEncoding LayeredFlowLP LayeredFlowDual Lax109476.LinearProgram
open BoundedDistances RegionRounding

def atTime {n L : ℕ} (y : Dual n L) (st : Edge n) (k : ℕ) (v : Fin n) : ℚ :=
  potential y st ⟨min k L,by omega⟩ v

@[simp] theorem atTime_zero {n L : ℕ} (y : Dual n L) (st : Edge n) (v : Fin n) :
    atTime y st 0 v=potential y st 0 v := by simp [atTime]

@[simp] theorem atTime_last {n L : ℕ} (y : Dual n L) (st : Edge n) (v : Fin n) :
    atTime y st L v=potential y st (Fin.last L) v := by simp [atTime,Fin.last]

theorem route_bound {n L : ℕ} (I : RationalInstance n) (y : Dual n L)
    (hy : DualFeasible (program I L) y) (st : Edge n) {k : ℕ} {c : ℚ}
    (hr : Route (length y) st.1 st.2 k c) (hk : k ≤ L) :
    potential y st (Fin.last L) st.2-potential y st 0 st.1 ≤ c := by
  obtain ⟨_,_,hdiag,hstep,_⟩ := geometry I y hy
  have hh : ∀ j,j < L → ∀ u v,atTime y st (j+1) v-atTime y st j u ≤ length y u v := by
    intro j hj u v
    simpa only [atTime,Nat.min_eq_left hj.le,Nat.min_eq_left (by omega : j+1 ≤ L),Fin.castSucc_mk,Fin.succ_mk] using
      hstep st (⟨j,hj⟩ : Fin L) u v
  simpa only [atTime_zero,atTime_last] using
    LayeredRouteBounds.padded_route_bound (length y) hdiag (atTime y st) L hh hr hk

/-- Duplicating the undirected capacity rows gives a symmetric length whose
weighted cost is twice the LP dual objective. -/
theorem cost_eq {n L : ℕ} (I : RationalInstance n)
    (hsym : ∀ u v,I.capacity u v=I.capacity v u) (y : Dual n L) :
    metricCost I (length y)=2*dualValue (program I L) y := by
  rw [objective_eq]
  have hterm (u v : Fin n) : (I.capacity u v : ℚ)*length y u v =
      (I.capacity u v : ℚ)*multiplier y u v+(I.capacity v u : ℚ)*multiplier y v u := by
    by_cases he : u=v
    · subst v; simp [I.loopless]
    · simp only [length,if_neg he,←hsym u v]
      ring
  change (∑ u,∑ v,(I.capacity u v : ℚ)*length y u v)=_
  simp_rw [hterm,Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun u v => (I.capacity v u : ℚ)*multiplier y v u)]
  ring

private theorem pair_sum {n : ℕ} (a : Fin n → ℚ) (b : ℚ) :
    (∑ u,∑ v,(a u+a v+b)/2)=(n : ℚ)*(∑ v,a v)+(n : ℚ)^2*b/2 := by
  simp_rw [add_div,Finset.sum_add_distrib]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
    ←Finset.sum_div,←Finset.mul_sum]
  ring

/-- The restricted path-distance constraint rules out a dual objective
below the required O(s/log n) flow value. -/
theorem objective_lower {n L : ℕ} (I : RationalInstance n) (hw : ∀ v,I.weight v=1)
    (hn : 2 ≤ n) (hI : ∀ u v,I.capacity u v=I.capacity v u)
    (s q : ℚ) (hs : 0 < s) (hq : 1/2 ≤ q) (hcut : UniformCutBounds.CutLower I s)
    (hrows : ∀ v,(∑ u,(I.capacity v u : ℚ)) ≤ q*n*s)
    (hL : 1024*(RegionBudget.steps n : ℚ)*q ≤ L ∨ n-1 ≤ L)
    (y : Dual n L) (hy : DualFeasible (program I L) y) :
    s/(2048*(RegionBudget.steps n : ℚ)) < dualValue (program I L) y := by
  by_contra hnot
  have hsmall := le_of_not_gt hnot
  have hcols (v : Fin n) : (∑ u,(I.capacity u v : ℚ)) ≤ q*n*s := by
    calc
      _ = ∑ u,(I.capacity v u : ℚ) := Finset.sum_congr rfl fun u _ => congrArg (fun x : ℚ≥0 => (x : ℚ)) (hI u v)
      _ ≤ _ := hrows v
  obtain ⟨hell,hsym,hdiag,_,hsep⟩ := geometry I y hy
  have hcost : metricCost I (length y) ≤ s/(1024*(RegionBudget.steps n : ℚ)) := by
    rw [cost_eq I hI y]
    have he : 2*(s/(2048*(RegionBudget.steps n : ℚ)))=s/(1024*(RegionBudget.steps n : ℚ)) := by ring
    linarith
  have hgeo : ∃ a : Fin n → ℚ, (∀ v,0 ≤ a v) ∧
      (∑ v,a v) ≤ 1/(128*(RegionBudget.steps n : ℚ)*n) ∧
      ∀ u v,∃ k ≤ L,∃ c ≤ a u+a v+1/(2*(n : ℚ)^2),Route (length y) u v k c := by
    rcases hL with hL | hL
    · exact ShortMetricGeometry.cheap_routes I hw hn s q hs hq hcut hrows hcols
        (length y) hell hdiag hsym hcost L hL
    · let H := ⌈1024*(RegionBudget.steps n : ℚ)*q⌉₊
      obtain ⟨a,ha,havg,hpaths⟩ := ShortMetricGeometry.cheap_routes I hw hn s q hs hq hcut hrows hcols
        (length y) hell hdiag hsym hcost H (Nat.le_ceil _)
      refine ⟨a,ha,havg,?_⟩
      intro u v
      obtain ⟨k,_,c,hc,hr⟩ := hpaths u v
      obtain ⟨k',hk',c',hc',hr'⟩ := RouteSimplification.shorten hell hr
      exact ⟨k',le_trans (hk'.trans (min_le_right _ _)) hL,c',hc'.trans hc,hr'⟩
  obtain ⟨a,ha,havg,hpaths⟩ := hgeo
  have hnq : (0 : ℚ) < n := by exact_mod_cast (show 0 < n by omega)
  have hK : (1 : ℚ) ≤ RegionBudget.steps n := by exact_mod_cast RegionBudget.steps_pos n
  have hsum : (∑ s,∑ t,if s=t then (0 : ℚ) else
      (potential y (s,t) (Fin.last L) t-potential y (s,t) 0 s)/2) ≤
      ∑ u,∑ v,(a u+a v+1/(2*(n : ℚ)^2))/2 := by
    apply Finset.sum_le_sum
    intro u _
    apply Finset.sum_le_sum
    intro v _
    by_cases he : u=v
    · simp only [if_pos he]
      exact div_nonneg (add_nonneg (add_nonneg (ha u) (ha v)) (by positivity)) (by norm_num)
    · rw [if_neg he]
      obtain ⟨k,hk,c,hc,hr⟩ := hpaths u v
      have hh := (route_bound I y hy (u,v) hr hk).trans hc
      exact div_le_div_of_nonneg_right hh (by norm_num)
  rw [pair_sum] at hsum
  have hconst : (n : ℚ)^2*(1/(2*(n : ℚ)^2))/2=1/4 := by field_simp <;> norm_num
  rw [hconst] at hsum
  have hupper := mul_le_mul_of_nonneg_left havg hnq.le
  have he : (n : ℚ)*(1/(128*(RegionBudget.steps n : ℚ)*n))=1/(128*(RegionBudget.steps n : ℚ)) := by field_simp
  rw [he] at hupper
  have hf : 1/(128*(RegionBudget.steps n : ℚ)) ≤ 1/128 := by
    apply (div_le_iff₀ (by positivity : (0 : ℚ) < 128*(RegionBudget.steps n : ℚ))).mpr
    linarith
  linarith

end Lax455465Proofs.LayeredDualBound
