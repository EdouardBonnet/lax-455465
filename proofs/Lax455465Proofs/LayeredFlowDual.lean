import Lax455465Proofs.LayeredFlowLP

open scoped BigOperators
namespace Lax455465Proofs.LayeredFlowDual
open Lax455465.RationalEncoding LayeredFlowLP Lax109476.LinearProgram

abbrev Dual (n L : ℕ) := Fin (n*n+2*((n*n)*((L+1)*n))) → ℚ

def multiplier {n L : ℕ} (y : Dual n L) (u v : Fin n) : ℚ := y (rowIndex n L (.inl (u,v)))

def length {n L : ℕ} (y : Dual n L) (u v : Fin n) : ℚ :=
  if u=v then 0 else multiplier y u v+multiplier y v u

def potential {n L : ℕ} (y : Dual n L) (st : Edge n) (k : Fin (L+1)) (u : Fin n) : ℚ :=
  y (rowIndex n L (.inr (0,(st,(k,u)))))-y (rowIndex n L (.inr (1,(st,(k,u)))))

theorem objective_eq {n L : ℕ} (I : RationalInstance n) (y : Dual n L) :
    dualValue (program I L) y=∑ u,∑ v,(I.capacity u v : ℚ)*multiplier y u v := by
  unfold dualValue
  rw [←Equiv.sum_comp (rowIndex n L)]
  simp [program,rowBound,multiplier,Fintype.sum_sum_type,Fintype.sum_prod_type]

private theorem usage_formula {n L : ℕ} (e : Edge n) (a : Arc n L) :
    usage e a=if a.2.2.1=a.2.2.2 then 0 else
      (if e=a.2.2 then 1 else 0)+(if e=(a.2.2.2,a.2.2.1) then 1 else 0) := by
  rcases e with ⟨u,v⟩
  rcases a with ⟨st,k,x,y⟩
  simp only [usage,Prod.mk.injEq]
  split_ifs <;> grind

/-- An advancing arc is constrained by the shared-edge length and the
potential difference between successive layers. Waiting arcs have length zero. -/
theorem arc_column {n L : ℕ} (I : RationalInstance n) (y : Dual n L)
    (st : Edge n) (k : Fin L) (u v : Fin n) :
    columnValue (program I L) y (variableIndex n L (.inr (st,(k,(u,v))))) =
      length y u v+potential y st k.castSucc u-potential y st k.succ v := by
  unfold columnValue
  rw [←Equiv.sum_comp (rowIndex n L)]
  by_cases huv : u=v
  · subst v
    simp [program,coefficient,balanceCoefficient,incidence,usage_formula,potential,length,multiplier,
      Fintype.sum_sum_type,Fintype.sum_prod_type,Fin.sum_univ_two,
      sub_mul,add_mul,Finset.sum_sub_distrib,Finset.sum_add_distrib,Finset.sum_ite_irrel,ite_and]
    ring
  · simp [program,coefficient,balanceCoefficient,incidence,usage_formula,potential,length,multiplier,
      Fintype.sum_sum_type,Fintype.sum_prod_type,Fin.sum_univ_two,
      sub_mul,add_mul,Finset.sum_sub_distrib,Finset.sum_add_distrib,Finset.sum_ite_irrel,ite_and,huv,Ne.symm huv]
    ring

/-- Only distinct commodities contribute, each with half a unit demand. -/
theorem value_column {n L : ℕ} (I : RationalInstance n) (y : Dual n L) :
    columnValue (program I L) y (variableIndex n L (.inl 0)) =
      ∑ s,∑ t,if s=t then 0 else (potential y (s,t) (Fin.last L) t-potential y (s,t) 0 s)/2 := by
  unfold columnValue
  rw [←Equiv.sum_comp (rowIndex n L)]
  simp [program,coefficient,balanceCoefficient,divergence,potential,
    Fintype.sum_sum_type,Fintype.sum_prod_type,Fin.sum_univ_two,
    sub_mul,Finset.sum_sub_distrib,Finset.sum_ite_irrel,ite_and]
  simp only [←Finset.sum_neg_distrib,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  by_cases hst : s=t <;> simp [hst] <;> ring

theorem geometry {n L : ℕ} (I : RationalInstance n) (y : Dual n L)
    (hy : DualFeasible (program I L) y) :
    (∀ u v,0 ≤ length y u v) ∧ (∀ u v,length y u v=length y v u) ∧
    (∀ u,length y u u=0) ∧
    (∀ st (k : Fin L) u v,potential y st k.succ v-potential y st k.castSucc u ≤ length y u v) ∧
    1 ≤ ∑ s,∑ t,if s=t then 0 else (potential y (s,t) (Fin.last L) t-potential y (s,t) 0 s)/2 := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro u v; dsimp [length,multiplier]; split_ifs <;> linarith [hy.1 (rowIndex n L (.inl (u,v))),hy.1 (rowIndex n L (.inl (v,u)))]
  · intro u v; by_cases he : u=v
    · subst v; rfl
    · simp [length,he,Ne.symm he,add_comm]
  · intro u; simp [length]
  · intro st k u v
    have hh := hy.2 (variableIndex n L (.inr (st,(k,(u,v)))))
    rw [arc_column] at hh
    have hc : (program I L).c (variableIndex n L (.inr (st,(k,(u,v)))))=0 := by simp [program,objective]
    rw [hc] at hh
    linarith
  · have hh := hy.2 (variableIndex n L (.inl 0))
    rw [value_column] at hh
    simpa only [program,Equiv.symm_apply_apply,objective] using hh

end Lax455465Proofs.LayeredFlowDual
