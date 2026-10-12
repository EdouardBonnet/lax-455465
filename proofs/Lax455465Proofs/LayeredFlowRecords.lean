import Lax455465Proofs.LayeredPathProjection
import Lax455465Proofs.PathRecordArithmetic

open scoped BigOperators
namespace Lax455465Proofs.LayeredFlowRecords
open Lax455465.RationalEncoding LayeredFlowLP LayeredFlowFeasibility
open AcyclicFlowDecomposition LayeredGraphFlow LayeredPathProjection PathSimplification

def combine {n : ℕ} (rs : Edge n → Records (Fin n)) : Records (Fin n) :=
  (List.ofFn fun j : Fin (n*n) => rs ((DirectedFlowLP.edgeIndex n).symm j)).flatten

theorem load_combine {n : ℕ} (rs : Edge n → Records (Fin n)) (u v : Fin n) :
    load (combine rs) u v=∑ st,load (rs st) u v := by
  rw [combine,PathRecordArithmetic.load_flatten]
  simp only [List.map_ofFn,List.sum_ofFn]
  rw [←Equiv.sum_comp (DirectedFlowLP.edgeIndex n)]
  simp

theorem routed_combine {n : ℕ} (rs : Edge n → Records (Fin n))
    (hv : ∀ st,Valid st.1 st.2 (rs st)) (s t : Fin n) :
    PathRecordArithmetic.routed (combine rs) s t=mass (rs (s,t)) := by
  rw [combine,PathRecordArithmetic.routed_flatten]
  simp only [List.map_ofFn,List.sum_ofFn]
  rw [←Equiv.sum_comp (DirectedFlowLP.edgeIndex n)]
  simp only [Function.comp_apply,Equiv.symm_apply_apply]
  change (∑ st,PathRecordArithmetic.routed (rs st) s t)=_
  calc
    _ = ∑ st : Edge n,if st.1=s ∧ st.2=t then mass (rs st) else 0 :=
      Finset.sum_congr rfl fun st _ => PathRecordArithmetic.routed_valid (hv st) s t
    _ = _ := by simp [Fintype.sum_prod_type,ite_and]

theorem mem_combine {n : ℕ} (rs : Edge n → Records (Fin n))
    (r : List (Fin n)×ℚ) : r∈combine rs ↔ ∃ st,r∈rs st := by
  simp only [combine,List.mem_flatten,List.mem_ofFn]
  constructor
  · rintro ⟨xs,⟨j,rfl⟩,hr⟩
    exact ⟨_,hr⟩
  · rintro ⟨st,hr⟩
    exact ⟨rs st,⟨DirectedFlowLP.edgeIndex n st,by simp⟩,hr⟩

theorem capacity_sum {n L : ℕ} (x : Arc n L → ℚ) (u v : Fin n) (huv : u ≠ v) :
    (∑ a,usage (u,v) a*x a)=
      ∑ st : Edge n,∑ k : Fin L,(x (st,(k,(u,v)))+x (st,(k,(v,u)))) := by
  simp only [usage,if_neg huv,add_mul,ite_mul,one_mul,zero_mul,
    Fintype.sum_prod_type,Prod.mk.injEq,ite_and,Finset.sum_add_distrib,
    Finset.sum_ite_irrel,Finset.sum_const_zero,Finset.sum_ite_eq',Finset.mem_univ,if_true]

/-- Every feasible layered LP vector has a polynomial-size collection of
simple physical paths with exactly its commodity demands. -/
theorem exists_records {n L : ℕ} (I : RationalInstance n) (f : ℚ) (x : Arc n L → ℚ)
    (h : Feasible I f x) :
    ∃ rs : Records (Fin n),
      (∀ r∈rs,0 < r.2 ∧ 2 ≤ r.1.length ∧ r.1.Nodup ∧ r.1.length ≤ L+1) ∧
      (∀ u v,load rs u v+load rs v u ≤ (I.capacity u v : ℚ)) ∧
      (∀ s t,s ≠ t → PathRecordArithmetic.routed rs s t=f/2) ∧
      rs.length ≤ n*n*(((L+1)*n)^2+1) := by
  have hex (st : Edge n) : ∃ rs : Records (Fin n),Valid st.1 st.2 rs ∧
      (∀ r∈rs,2 ≤ r.1.length ∧ r.1.length ≤ L+1) ∧
      (∀ u v,load rs u v ≤ ∑ k : Fin L,x (st,(k,(u,v)))) ∧
      (st.1 ≠ st.2 → mass rs=f/2) ∧ rs.length ≤ ((L+1)*n)^2+1 := by
    by_cases hst : st.1=st.2
    · refine ⟨[],by simp [Valid],by simp,?_,by simp [hst],by simp⟩
      intro u v
      exact Finset.sum_nonneg fun k _ => h.2.1 _
    · obtain ⟨rs,hvalid,hmass,hload,hlen⟩ := decompose I f x h st.1 st.2 hst
      refine ⟨project rs,valid_project st.1 st.2 rs hvalid,?_,?_,?_,?_⟩
      · intro r hr
        have hv := valid_project st.1 st.2 rs hvalid r hr
        have he := distinct_endpoints hst hv.2.1 hv.2.2.1
        have hn := hv.2.2.2
        have hlen' : 2 ≤ r.1.length := by
          have hh := length_le r.1
          omega
        exact ⟨hlen',length_project x h.2.1 st.1 st.2 rs hvalid hload r hr⟩
      · exact load_le x st rs (fun r hr => (hvalid r hr).1.le) hload
      · intro _
        rwa [mass_project]
      · simpa [project] using hlen
  choose rs hvalid hlength hload hmass hcount using hex
  refine ⟨combine rs,?_,?_,?_,?_⟩
  · intro r hr
    obtain ⟨st,hr⟩ := (mem_combine rs r).mp hr
    exact ⟨(hvalid st r hr).1,(hlength st r hr).1,(hvalid st r hr).2.2.2,(hlength st r hr).2⟩
  · intro u v
    by_cases he : u=v
    · subst v
      have hn : ∀ r∈combine rs,r.1.Nodup := by
        intro r hr
        obtain ⟨st,hr⟩ := (mem_combine rs r).mp hr
        exact (hvalid st r hr).2.2.2
      rw [PathRecordArithmetic.load_loop_zero _ hn,zero_add,I.loopless]
      rfl
    · rw [load_combine,load_combine,←Finset.sum_add_distrib]
      calc
        _ ≤ ∑ st : Edge n,∑ k : Fin L,(x (st,(k,(u,v)))+x (st,(k,(v,u)))) := by
          apply Finset.sum_le_sum
          intro st _
          rw [Finset.sum_add_distrib]
          exact add_le_add (hload st u v) (hload st v u)
        _ = ∑ a,usage (u,v) a*x a := (capacity_sum x u v he).symm
        _ ≤ _ := h.2.2.1 (u,v)
  · intro s t hst
    rw [routed_combine rs hvalid]
    exact hmass (s,t) hst
  · simp only [combine,List.length_flatten,List.map_map,List.map_ofFn,List.sum_ofFn]
    have hh : (∑ j : Fin (n*n),(rs ((DirectedFlowLP.edgeIndex n).symm j)).length) ≤
        ∑ _j : Fin (n*n),(((L+1)*n)^2+1) :=
      Finset.sum_le_sum fun j _ => hcount _
    simpa using hh

end Lax455465Proofs.LayeredFlowRecords
