import Lax455465Proofs.LayeredFlowLP

open scoped BigOperators
namespace Lax455465Proofs.LayeredFlowFeasibility
open Lax455465.RationalEncoding LayeredFlowLP Lax109476.LinearProgram

/-- Typed shared capacities and exact conservation in the layered network. -/
def Feasible {n L : ℕ} (I : RationalInstance n) (f : ℚ) (x : Arc n L → ℚ) : Prop :=
  0 ≤ f ∧ (∀ a, 0 ≤ x a) ∧
  (∀ e : Edge n, (∑ a, usage e a*x a) ≤ (I.capacity e.1 e.2 : ℚ)) ∧
  ∀ b : Balance n L, (∑ a, incidence b a*x a)=f*divergence b

theorem vector_representation {n L : ℕ}
    (z : Fin (1+(n*n)*(L*(n*n))) → ℚ) :
    vector (z (variableIndex n L (.inl 0)))
      (fun a => z (variableIndex n L (.inr a)))=z := by
  funext j
  obtain ⟨v,rfl⟩ := (variableIndex n L).surjective j
  cases v with
  | inl i =>
    have hi : i=0 := Subsingleton.elim _ _
    subst i
    simp [vector]
  | inr a => simp [vector]

theorem capacity_row {n L : ℕ} (I : RationalInstance n) (f : ℚ)
    (x : Arc n L → ℚ) (e : Edge n) :
    rowValue (program I L) (vector f x) (rowIndex n L (.inl e))=
      ∑ a,usage e a*x a := by
  unfold rowValue
  rw [←Equiv.sum_comp (variableIndex n L)]
  simp [program,vector,coefficient,Fintype.sum_sum_type]

theorem balance_row {n L : ℕ} (I : RationalInstance n) (f : ℚ)
    (x : Arc n L → ℚ) (b : Balance n L) (sign : Fin 2) :
    rowValue (program I L) (vector f x) (rowIndex n L (.inr (sign,b)))=
      (if sign=0 then 1 else -1)*((∑ a,incidence b a*x a)-f*divergence b) := by
  unfold rowValue
  rw [←Equiv.sum_comp (variableIndex n L)]
  by_cases hs : sign=0 <;>
    simp [program,vector,coefficient,balanceCoefficient,Fintype.sum_sum_type,hs,
      Finset.sum_neg_distrib] <;> ring

theorem feasible_iff {n L : ℕ} (I : RationalInstance n) (f : ℚ)
    (x : Arc n L → ℚ) :
    PrimalFeasible (program I L) (vector f x) ↔ Feasible I f x := by
  constructor
  · rintro ⟨hpos,hrows⟩
    refine ⟨?_,?_,?_,?_⟩
    · simpa [vector] using hpos (variableIndex n L (.inl 0))
    · intro a
      simpa [vector] using hpos (variableIndex n L (.inr a))
    · intro e
      have h := hrows (rowIndex n L (.inl e))
      rw [capacity_row] at h
      simpa only [program,Equiv.symm_apply_apply,rowBound] using h
    · intro b
      have hp := hrows (rowIndex n L (.inr (0,b)))
      have hn := hrows (rowIndex n L (.inr (1,b)))
      rw [balance_row] at hp hn
      norm_num [program,rowBound] at hp hn
      linarith
  · rintro ⟨hf,hx,hcap,hbal⟩
    constructor
    · intro j
      simp only [vector]
      cases (variableIndex n L).symm j with
      | inl _ => exact hf
      | inr a => exact hx a
    · intro i
      obtain ⟨r,rfl⟩ := (rowIndex n L).surjective i
      cases r with
      | inl e =>
        rw [capacity_row]
        simpa only [program,Equiv.symm_apply_apply,rowBound] using hcap e
      | inr b =>
        rw [balance_row,hbal]
        simp [program,rowBound]

/-- Incidence at a fixed vertex is outgoing mass minus incoming mass. -/
theorem incidence_sum {n L : ℕ} (x : Arc n L → ℚ) (st : Edge n)
    (j : Fin (L+1)) (u : Fin n) :
    (∑ a,incidence (st,(j,u)) a*x a)=
      (∑ k : Fin L,if k.castSucc=j then ∑ v,x (st,(k,(u,v))) else 0)-
      (∑ k : Fin L,if k.succ=j then ∑ v,x (st,(k,(v,u))) else 0) := by
  rcases st with ⟨s,t⟩
  simp only [incidence,Fintype.sum_prod_type,Prod.mk.injEq,ite_mul,zero_mul,sub_mul,
    one_mul,ite_and,Finset.sum_ite_irrel,Finset.sum_ite_eq',Finset.mem_univ,if_true,
    Finset.sum_sub_distrib,Finset.sum_const_zero]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : k.castSucc=j
  · simp only [if_pos hk]
    rw [Finset.sum_comm]
    simp
  · simp [hk]

end Lax455465Proofs.LayeredFlowFeasibility
