import Lax455465Proofs.LayeredPathSweep
import Lax455465Proofs.AdjacentOfFn
import Lax455465Proofs.PathSubtraction
import Lax455465Proofs.LayeredWalkState

namespace Lax455465Proofs.LayeredSweepGraph
open LayeredFlowLP LayeredGraphFlow LayeredWalkState LayeredPathSweep PathSimplification
open scoped NNRat BigOperators

def raw {n L : ℕ} (path : Fin (L+1) → Fin n) : List (Vertex n L) :=
  List.ofFn fun i => (i,path i)

theorem count_list {α : Type*} [BEq α] [LawfulBEq α] [DecidableEq α] (xs : List α) (a : α) :
    xs.count a=(xs.map fun b => if b=a then (1 : ℕ) else 0).sum := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    simp only [List.count_cons,List.map_cons,List.sum_cons,ih]
    by_cases he : b=a
    · subst b
      simp [Nat.add_comm]
    · have hne : a≠b := Ne.symm he
      simp [he,hne,Nat.add_comm]

theorem count_ofFn {α : Type*} [BEq α] [LawfulBEq α] [DecidableEq α] {N : ℕ} (f : Fin N → α) (a : α) :
    (List.ofFn f).count a=(List.ofFn fun i => if f i=a then (1 : ℕ) else 0).sum := by
  rw [count_list,List.map_ofFn]
  rfl

theorem raw_count {n L : ℕ} (path : Fin (L+1) → Fin n) (p q : Vertex n L) :
    PathCounting.count (raw path) p q=∑ k : Fin L,
      if k.castSucc=p.1 ∧ k.succ=q.1 ∧ path k.castSucc=p.2 ∧ path k.succ=q.2 then (1 : ℚ) else 0 := by
  letI : BEq (Vertex n L) := instBEqOfDecidableEq
  unfold PathCounting.count raw
  rw [AdjacentOfFn.arcs,count_ofFn,List.sum_ofFn]
  push_cast
  apply Finset.sum_congr rfl
  intro k _
  simp only [Prod.mk.injEq,ite_and]
  split_ifs <;> simp_all [Prod.ext_iff]

theorem processed_arc {n L : ℕ} (st : Edge n) (path : Fin (L+1) → Fin n) (k : Fin L) (u v : Fin n) :
    Processed st path L (variableIndex n L (.inr (st,(k,(u,v))))) ↔
      u=path k.castSucc ∧ v=path k.succ := by
  constructor
  · rintro ⟨l,hl,he⟩
    have hh := Sum.inr.inj ((variableIndex n L).injective he)
    have hk : k=l := congrArg (fun a : Arc n L => a.2.1) hh
    subst l
    exact ⟨congrArg (fun a : Arc n L => a.2.2.1) hh,congrArg (fun a : Arc n L => a.2.2.2) hh⟩
  · rintro ⟨rfl,rfl⟩
    exact ⟨k,k.isLt,rfl⟩

theorem arc_after {n L : ℕ} (q : Coordinate n L → ℚ≥0) (w : ℚ≥0)
    (st : Edge n) (path : Fin (L+1) → Fin n)
    (hw : ∀ k,w≤q (edge st path k)) (k : Fin L) (u v : Fin n) :
    arc (after q w st path L) (st,(k,(u,v)))=
      arc q (st,(k,(u,v)))-(if u=path k.castSucc ∧ v=path k.succ then (w : ℚ) else 0) := by
  unfold arc after
  simp only [processed_arc]
  by_cases he : u=path k.castSucc ∧ v=path k.succ
  · rcases he with ⟨rfl,rfl⟩
    simp only [if_true]
    have hh : (w : ℚ)≤(q (edge st path k) : ℚ) := by exact_mod_cast hw k
    change max ((q (edge st path k) : ℚ)-(w : ℚ)) 0=(q (edge st path k) : ℚ)-(w : ℚ)
    exact max_eq_left (sub_nonneg.mpr hh)
  · simp only [if_neg he,sub_zero]

/-- The actual coordinate sweep is exactly ordinary path subtraction in
the layered graph, so the existing conservation and load proofs apply. -/
theorem graph_after {n L : ℕ} (q : Coordinate n L → ℚ≥0) (w : ℚ≥0)
    (st : Edge n) (path : Fin (L+1) → Fin n) (hw : ∀ k,w≤q (edge st path k)) :
    graph (arc (after q w st path L)) st=
      PathSubtraction.residual (graph (arc q) st) (raw path) (w : ℚ) := by
  funext p r
  have he (k : Fin L) :
      (if k.castSucc=p.1 ∧ k.succ=r.1 then arc (after q w st path L) (st,(k,(p.2,r.2))) else 0)=
      (if k.castSucc=p.1 ∧ k.succ=r.1 then arc q (st,(k,(p.2,r.2))) else 0)-
      (w : ℚ)*(if k.castSucc=p.1 ∧ k.succ=r.1 ∧ path k.castSucc=p.2 ∧ path k.succ=r.2 then 1 else 0) := by
    rw [arc_after q w st path hw]
    split_ifs <;> grind
  have hsum := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl (fun k _ => he k)
  rw [Finset.sum_sub_distrib,←Finset.mul_sum] at hsum
  simpa only [PathSubtraction.residual,graph,raw_count] using hsum

@[simp] theorem raw_head {n L : ℕ} (path : Fin (L+1) → Fin n) :
    (raw path).head?=some (0,path 0) := by
  simp only [raw,List.ofFn_succ,List.head?_cons]

@[simp] theorem raw_last {n L : ℕ} (path : Fin (L+1) → Fin n) :
    (raw path).getLast?=some (Fin.last L,path (Fin.last L)) := by
  have hne : raw path≠[] := by simp [raw]
  rw [List.getLast?_eq_some_getLast hne]
  simp only [raw,List.getLast_ofFn,Nat.add_sub_cancel]
  rfl

theorem raw_levels {n L : ℕ} (path : Fin (L+1) → Fin n) : PositiveWalk.Levels (raw path) := by
  simp only [PositiveWalk.Levels,raw,List.map_ofFn,List.length_ofFn]
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_ofFn,List.getElem_range]
    rfl

theorem raw_nodup {n L : ℕ} (path : Fin (L+1) → Fin n) : (raw path).Nodup :=
  PositiveWalk.nodup (raw_levels path)

theorem balance_after {n L : ℕ} (q : Coordinate n L → ℚ≥0) (w : ℚ≥0)
    (st : Edge n) (path : Fin (L+1) → Fin n) (hw : ∀ k,w≤q (edge st path k))
    (hs : path 0=st.1) (ht : path (Fin.last L)=st.2) (a : ℚ)
    (hb : AcyclicFlowPath.Balance (graph (arc q) st) (0,st.1) (Fin.last L,st.2) a) :
    AcyclicFlowPath.Balance (graph (arc (after q w st path L)) st) (0,st.1) (Fin.last L,st.2) (a-(w : ℚ)) := by
  rw [graph_after q w st path hw]
  exact PathSubtraction.residual_balance _ _ _ a hb (raw path)
    (by simpa only [raw_head,hs]) (by simpa only [raw_last,ht]) (w : ℚ)

theorem other_arc {n L : ℕ} (q : Coordinate n L → ℚ≥0) (w : ℚ≥0)
    (st other : Edge n) (path : Fin (L+1) → Fin n) (hother : other≠st) (i : ℕ)
    (k : Fin L) (u v : Fin n) :
    arc (after q w st path i) (other,(k,(u,v)))=arc q (other,(k,(u,v))) := by
  have hh : ¬Processed st path i (variableIndex n L (.inr (other,(k,(u,v))))) := by
    rintro ⟨l,hl,he⟩
    have hp := Sum.inr.inj ((variableIndex n L).injective he)
    exact hother (congrArg (fun a : Arc n L => a.1) hp)
  simp only [arc,after,if_neg hh]

theorem other_graph {n L : ℕ} (q : Coordinate n L → ℚ≥0) (w : ℚ≥0)
    (st other : Edge n) (path : Fin (L+1) → Fin n) (hother : other≠st) (i : ℕ) :
    graph (arc (after q w st path i)) other=graph (arc q) other := by
  funext p r
  simp only [graph,other_arc q w st other path hother i]

theorem value_unchanged {n L : ℕ} (q : Coordinate n L → ℚ≥0) (w : ℚ≥0)
    (st : Edge n) (path : Fin (L+1) → Fin n) (i : ℕ) :
    after q w st path i (variableIndex n L (.inl 0))=q (variableIndex n L (.inl 0)) := by
  have hh : ¬Processed st path i (variableIndex n L (.inl 0)) := by
    rintro ⟨k,hk,he⟩
    have hc := (variableIndex n L).injective he
    cases hc
  simp only [after,if_neg hh]

end Lax455465Proofs.LayeredSweepGraph
