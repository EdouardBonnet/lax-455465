import Lax455465Proofs.LayeredFlowDual
import Lax455465Proofs.LayeredFlowFeasibility
import Lax109476.PolynomialTimeSolver

open scoped BigOperators
namespace Lax455465Proofs.LayeredFlowBounds
open Lax455465.RationalEncoding LayeredFlowLP LayeredFlowDual LayeredFlowFeasibility
open Lax109476.LinearProgram Lax109476.RationalCertificates
open Lax109476.FarkasCertificate Lax109476.RecessionDirection

theorem dual_of_geometry {n L : ℕ} (I : RationalInstance n) (y : Dual n L)
    (hy : ∀ i,0 ≤ y i)
    (hstep : ∀ st (k : Fin L) u v,
      potential y st k.succ v-potential y st k.castSucc u ≤ length y u v)
    (hsep : 1 ≤ ∑ s,∑ t,if s=t then 0 else
      (potential y (s,t) (Fin.last L) t-potential y (s,t) 0 s)/2) :
    DualFeasible (program I L) y := by
  refine ⟨hy,?_⟩
  intro j
  obtain ⟨v,rfl⟩ := (variableIndex n L).surjective j
  cases v with
  | inl i =>
    have hi : i=0 := Subsingleton.elim _ _
    subst i
    rw [value_column]
    simpa [program,objective] using hsep
  | inr a =>
    rcases a with ⟨st,k,u,v⟩
    rw [arc_column]
    simp only [program,Equiv.symm_apply_apply,objective]
    linarith [hstep st k u v]

/-- A single commodity supplies a feasible dual, at every layer budget. -/
def boundedDual {n L : ℕ} (s t : Fin n) : Dual n L := fun i =>
  match (rowIndex n L).symm i with
  | .inl _ => 1
  | .inr (sign,st,_,v) => if sign=0 ∧ st=(s,t) ∧ v=t then 2 else 0

@[simp] theorem boundedDual_length {n L : ℕ} (s t u v : Fin n) :
    length (boundedDual (L := L) s t) u v=if u=v then 0 else 2 := by
  norm_num [length,multiplier,boundedDual]

@[simp] theorem boundedDual_potential {n L : ℕ} (s t : Fin n)
    (st : Edge n) (k : Fin (L+1)) (v : Fin n) :
    potential (boundedDual s t) st k v=if st=(s,t) ∧ v=t then 2 else 0 := by
  simp [potential,boundedDual]

theorem boundedDual_feasible {n L : ℕ} (I : RationalInstance n)
    (s t : Fin n) (hst : s ≠ t) :
    DualFeasible (program I L) (boundedDual s t) := by
  apply dual_of_geometry
  · intro i
    simp only [boundedDual]
    cases (rowIndex n L).symm i with
    | inl e => norm_num
    | inr b =>
      rcases b with ⟨sign,st,k,v⟩
      dsimp only
      split_ifs <;> norm_num
  · intro st k u v
    simp only [boundedDual_potential,boundedDual_length]
    split_ifs <;> grind
  · have he (u v : Fin n) :
        (if u=v then (0 : ℚ) else
          ((if (u,v)=(s,t) ∧ v=t then 2 else 0)-
           (if (u,v)=(s,t) ∧ u=t then 2 else 0))/2)=
        if u=s ∧ v=t then 1 else 0 := by
      simp only [Prod.mk.injEq]
      split_ifs <;> grind
    simp only [boundedDual_potential,he]
    simp [ite_and]

theorem no_infeasibility_certificate {n L : ℕ} (I : RationalInstance n)
    (y : Dual n L) : ¬ IsInfeasibilityCertificate (program I L) y := by
  intro h
  have hb : ∀ i,0 ≤ (program I L).b i := by
    intro i
    simp only [program]
    cases (rowIndex n L).symm i <;> simp only [rowBound] <;> positivity
  have hh : 0 ≤ dualValue (program I L) y :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hb i) (h.1 i)
  exact (not_lt_of_ge hh) h.2.2

/-- A dual-feasible vector rules out an improving recession direction. -/
theorem no_direction_of_dual {m n : ℕ} (P : Program ℚ m n)
    (y : Fin m → ℚ) (hy : DualFeasible P y) (d : Fin n → ℚ) :
    ¬ IsImprovingDirection P d := by
  intro hd
  have hobj : primalValue P d ≤ ∑ j,columnValue P y j*d j :=
    Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hy.2 j) (hd.1 j)
  have he : (∑ j,columnValue P y j*d j)=∑ i,y i*rowValue P d i := by
    simp only [columnValue,rowValue,Finset.sum_mul,Finset.mul_sum]
    rw [Finset.sum_comm]
    congr 1
    funext i
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he] at hobj
  have hzero : (∑ i,y i*rowValue P d i) ≤ 0 :=
    Finset.sum_nonpos fun i _ => mul_nonpos_of_nonneg_of_nonpos (hy.1 i) (hd.2.1 i)
  linarith [hd.2.2]

theorem no_improving_direction {n L : ℕ} (I : RationalInstance n) (hn : 2 ≤ n)
    (d : Fin (1+(n*n)*(L*(n*n))) → ℚ) :
    ¬ IsImprovingDirection (program I L) d := by
  let s : Fin n := ⟨0,by omega⟩
  let t : Fin n := ⟨1,by omega⟩
  exact no_direction_of_dual _ _ (boundedDual_feasible I s t (by simp [s,t])) d

/-- The registered exact LP algorithm returns an optimal layered flow and
a matching dual; infeasibility and unboundedness are impossible. -/
theorem exact_optimal_pair {n : ℕ} (I : RationalInstance n) (hn : 2 ≤ n) (L : ℕ) :
    ∃ (f : ℚ) (x : Arc n L → ℚ) (y : Dual n L),
      Feasible I f x ∧ DualFeasible (program I L) y ∧ f=dualValue (program I L) y := by
  obtain ⟨solve,_,hsolve⟩ := Lax109476.PolynomialTimeSolver.exists_exact_polynomial_time_solver
  obtain ⟨cert,_,hvalid⟩ := hsolve _ _ (program I L)
  cases cert with
  | optimal z y =>
    rcases hvalid with ⟨hz,hy,hval⟩
    let f := z (variableIndex n L (.inl 0))
    let x := fun a => z (variableIndex n L (.inr a))
    have hrepr : vector f x=z := vector_representation z
    refine ⟨f,x,y,?_,hy,?_⟩
    · rw [←hrepr,feasible_iff] at hz
      exact hz
    · rw [←hrepr,objective_value] at hval
      exact hval
  | infeasible y => exact False.elim (no_infeasibility_certificate I y hvalid)
  | unbounded z d => exact False.elim (no_improving_direction I hn d hvalid.2)

end Lax455465Proofs.LayeredFlowBounds
