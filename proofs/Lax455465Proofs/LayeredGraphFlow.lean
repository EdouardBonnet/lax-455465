import Lax455465Proofs.LayeredFlowFeasibility
import Lax455465Proofs.AcyclicFlowDecomposition

open scoped BigOperators
namespace Lax455465Proofs.LayeredGraphFlow
open Lax455465.RationalEncoding LayeredFlowLP LayeredFlowFeasibility
open AcyclicFlowPath AcyclicFlowDecomposition PathSimplification

abbrev Vertex (n L : ℕ) := Fin (L+1)×Fin n

/-- The ordinary acyclic graph represented by one commodity of the layered LP. -/
def graph {n L : ℕ} (x : Arc n L → ℚ) (st : Edge n) (p q : Vertex n L) : ℚ :=
  ∑ k : Fin L,if k.castSucc=p.1 ∧ k.succ=q.1 then x (st,(k,(p.2,q.2))) else 0

theorem nonnegative {n L : ℕ} (x : Arc n L → ℚ) (hx : ∀ a,0 ≤ x a)
    (st : Edge n) (p q : Vertex n L) : 0 ≤ graph x st p q := by
  apply Finset.sum_nonneg
  intro k _
  split_ifs
  · exact hx _
  · rfl

/-- Every positive arc advances the layer by exactly one, including waits
at the same physical vertex. -/
theorem advances {n L : ℕ} (x : Arc n L → ℚ) (hx : ∀ a,0 ≤ x a)
    (st : Edge n) (p q : Vertex n L) (h : 0 < graph x st p q) :
    q.1.val=p.1.val+1 := by
  obtain ⟨k,_,hk⟩ := (Finset.sum_pos_iff_of_nonneg (fun k _ =>
    show 0 ≤ if k.castSucc=p.1 ∧ k.succ=q.1 then x (st,(k,(p.2,q.2))) else 0 by
      split_ifs <;> [exact hx _; exact le_rfl])).mp h
  split_ifs at hk with he
  · rw [←he.1,←he.2]
    rfl
  · exact (lt_irrefl _ hk).elim

theorem outgoing {n L : ℕ} (x : Arc n L → ℚ) (st : Edge n) (p : Vertex n L) :
    (∑ q,graph x st p q)=
      ∑ k : Fin L,if k.castSucc=p.1 then ∑ v,x (st,(k,(p.2,v))) else 0 := by
  simp only [graph,Fintype.sum_prod_type]
  simp_rw [Finset.sum_comm (f := fun (v : Fin n) (k : Fin L) =>
    if k.castSucc=p.1 ∧ k.succ=(_ : Fin (L+1)) then x (st,(k,(p.2,v))) else 0)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : k.castSucc=p.1
  · simp only [hk,ite_true,true_and]
    rw [Finset.sum_comm]
    simp
  · simp [hk]

theorem incoming {n L : ℕ} (x : Arc n L → ℚ) (st : Edge n) (q : Vertex n L) :
    (∑ p,graph x st p q)=
      ∑ k : Fin L,if k.succ=q.1 then ∑ u,x (st,(k,(u,q.2))) else 0 := by
  simp only [graph,Fintype.sum_prod_type]
  simp_rw [Finset.sum_comm (f := fun (u : Fin n) (k : Fin L) =>
    if k.castSucc=(_ : Fin (L+1)) ∧ k.succ=q.1 then x (st,(k,(u,q.2))) else 0)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : k.succ=q.1
  · simp only [hk,ite_true,and_true]
    rw [Finset.sum_comm]
    simp
  · simp [hk]

theorem balance {n L : ℕ} (I : RationalInstance n) (f : ℚ) (x : Arc n L → ℚ)
    (h : Feasible I f x) (s t : Fin n) (hst : s ≠ t) :
    Balance (graph x (s,t)) (0,s) (Fin.last L,t) (f/2) := by
  intro p
  rw [outgoing,incoming,←incidence_sum]
  rw [h.2.2.2]
  simp only [divergence,if_neg hst,Prod.mk.injEq,Prod.ext_iff]
  split_ifs <;> ring

/-- Each commodity has a polynomial number of rational path records in
the layered graph. Subsequent projection and cycle erasure preserve loads. -/
theorem decompose {n L : ℕ} (I : RationalInstance n) (f : ℚ) (x : Arc n L → ℚ)
    (h : Feasible I f x) (s t : Fin n) (hst : s ≠ t) :
    ∃ rs : Records (Vertex n L),Valid (0,s) (Fin.last L,t) rs ∧ mass rs=f/2 ∧
      (∀ p q,load rs p q ≤ graph x (s,t) p q) ∧
      rs.length ≤ ((L+1)*n)^2+1 := by
  have hne : ((0,s) : Vertex n L) ≠ (Fin.last L,t) := by
    intro he
    exact hst (congrArg Prod.snd he)
  obtain ⟨rs,hvalid,hmass,hload,hlen⟩ := exists_records (graph x (s,t))
    (nonnegative x h.2.1 (s,t)) (fun p => p.1.val) L (fun p => by omega)
    (fun p q hpq => by have hh := advances x h.2.1 (s,t) p q hpq; omega)
    (0,s) (Fin.last L,t) hne (f/2) (by linarith [h.1]) (balance I f x h s t hst)
  refine ⟨rs,hvalid,hmass,hload,?_⟩
  have hc := Finset.card_le_univ (PathSubtraction.support (graph x (s,t)))
  simp only [Fintype.card_prod,Fintype.card_fin] at hc
  nlinarith

end Lax455465Proofs.LayeredGraphFlow
