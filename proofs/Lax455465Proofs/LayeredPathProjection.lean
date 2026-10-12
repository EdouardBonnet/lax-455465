import Lax455465Proofs.LayeredGraphFlow

open scoped BigOperators
namespace Lax455465Proofs.LayeredPathProjection
open Lax455465.RationalEncoding LayeredFlowLP LayeredFlowFeasibility
open AcyclicFlowDecomposition LayeredGraphFlow PathSimplification

/-- Projection followed by cycle erasure removes both waits and repeated
physical vertices while preserving the path's endpoints. -/
def path {n L : ℕ} (xs : List (Vertex n L)) : List (Fin n) := simplify (xs.map Prod.snd)
def project {n L : ℕ} (rs : Records (Vertex n L)) : Records (Fin n) :=
  rs.map fun r => (path r.1,r.2)

theorem count_map {n L : ℕ} (xs : List (Vertex n L)) (u v : Fin n) :
    PathCounting.count (xs.map Prod.snd) u v=
      ∑ j : Fin (L+1),∑ k : Fin (L+1),PathCounting.count xs (j,u) (k,v) := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    cases xs with
    | nil => simp
    | cons b xs =>
      simp only [List.map_cons,PathCounting.count_cons_cons,Finset.sum_add_distrib]
      simp only [List.map_cons] at ih
      rw [ih]
      congr 1
      rcases a with ⟨i,a⟩
      rcases b with ⟨j,b⟩
      by_cases hau : a=u <;> by_cases hbv : b=v <;>
        simp [Prod.mk.injEq,hau,hbv,ite_and,Finset.sum_ite_irrel]

theorem count_path_le {n L : ℕ} (xs : List (Vertex n L)) (u v : Fin n) :
    PathCounting.count (path xs) u v ≤
      ∑ j : Fin (L+1),∑ k : Fin (L+1),PathCounting.count xs (j,u) (k,v) := by
  rw [←count_map]
  unfold PathCounting.count path
  exact_mod_cast arc_count_le (xs.map Prod.snd) u v

theorem mass_project {n L : ℕ} (rs : Records (Vertex n L)) : mass (project rs)=mass rs := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simpa [project,mass] using congrArg (fun z : ℚ => r.2+z) ih

theorem load_project_le {n L : ℕ} (rs : Records (Vertex n L))
    (hpos : ∀ r∈rs,0 ≤ r.2) (u v : Fin n) :
    load (project rs) u v ≤ ∑ j : Fin (L+1),∑ k : Fin (L+1),load rs (j,u) (k,v) := by
  induction rs with
  | nil => simp [project]
  | cons r rs ih =>
    have hw := hpos r (by simp)
    have ht : ∀ r'∈rs,0 ≤ r'.2 := fun r' hr' => hpos r' (by simp [hr'])
    have hh := mul_le_mul_of_nonneg_left (count_path_le r.1 u v) hw
    simp only [Finset.mul_sum] at hh
    have ht' := ih ht
    simp only [project,List.map_cons,load_cons,Finset.sum_add_distrib]
    exact add_le_add hh ht'

theorem graph_sum_layers {n L : ℕ} (x : Arc n L → ℚ) (st : Edge n) (u v : Fin n) :
    (∑ i : Fin (L+1),∑ j : Fin (L+1),graph x st (i,u) (j,v))=
      ∑ k : Fin L,x (st,(k,(u,v))) := by
  simp only [graph]
  simp_rw [Finset.sum_comm (f := fun (j : Fin (L+1)) (k : Fin L) =>
    if k.castSucc=(_ : Fin (L+1)) ∧ k.succ=j then x (st,(k,(u,v))) else 0)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  simp [ite_and,Finset.sum_ite_irrel]

theorem load_le {n L : ℕ} (x : Arc n L → ℚ) (st : Edge n)
    (rs : Records (Vertex n L)) (hpos : ∀ r∈rs,0 ≤ r.2)
    (hload : ∀ p q,load rs p q ≤ graph x st p q) (u v : Fin n) :
    load (project rs) u v ≤ ∑ k : Fin L,x (st,(k,(u,v))) := by
  calc
    _ ≤ ∑ j : Fin (L+1),∑ k : Fin (L+1),load rs (j,u) (k,v) := load_project_le rs hpos u v
    _ ≤ ∑ j : Fin (L+1),∑ k : Fin (L+1),graph x st (j,u) (k,v) :=
      Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => hload _ _
    _ = _ := graph_sum_layers x st u v

theorem valid_project {n L : ℕ} (s t : Fin n) (rs : Records (Vertex n L))
    (hvalid : Valid (0,s) (Fin.last L,t) rs) : Valid s t (project rs) := by
  intro r hr
  obtain ⟨r',hr',rfl⟩ := List.mem_map.mp hr
  obtain ⟨hw,hs,ht,hn⟩ := hvalid r' hr'
  refine ⟨hw,?_,?_,nodup _⟩
  · simp [path,List.head?_map,hs]
  · simp [path,List.getLast?_map,ht]

theorem advancing_length {α : Type*} [DecidableEq α] (rank : α → ℕ)
    {xs : List α} {s t : α} (hs : xs.head?=some s) (ht : xs.getLast?=some t)
    (hstep : ∀ e∈arcs xs,rank e.2=rank e.1+1) : rank t+1=rank s+xs.length := by
  induction xs generalizing s with
  | nil => simp at hs
  | cons a xs ih =>
    have ha : a=s := by simpa using hs
    subst a
    cases xs with
    | nil =>
      have hh : s=t := by simpa using ht
      subst t
      simp
    | cons b xs =>
      have hsb := hstep (s,b) (by simp)
      dsimp only at hsb
      have hh := ih rfl (by simpa using ht) (fun e he => hstep e (by simp [he]))
      simp only [List.length_cons] at hh ⊢
      omega

theorem length_project {n L : ℕ} (x : Arc n L → ℚ) (hx : ∀ a,0 ≤ x a)
    (s t : Fin n) (rs : Records (Vertex n L))
    (hvalid : Valid (0,s) (Fin.last L,t) rs)
    (hload : ∀ p q,load rs p q ≤ graph x (s,t) p q)
    (r : List (Fin n)×ℚ) (hr : r∈project rs) : r.1.length ≤ L+1 := by
  obtain ⟨r',hr',rfl⟩ := List.mem_map.mp hr
  obtain ⟨hw,hs,ht,hn⟩ := hvalid r' hr'
  have hh := advancing_length (fun p : Vertex n L => p.1.val) hs ht (fun e he =>
    advances x hx (s,t) e.1 e.2 (record_supported _ hvalid hload r' hr' e he))
  have hl := length_le (r'.1.map Prod.snd)
  simp only [List.length_map,Fin.val_zero,Fin.val_last,Nat.zero_add] at hh hl
  exact hl.trans hh.symm.le

end Lax455465Proofs.LayeredPathProjection
