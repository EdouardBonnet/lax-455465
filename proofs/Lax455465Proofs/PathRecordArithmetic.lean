import Lax455465Proofs.AcyclicFlowDecomposition

open scoped BigOperators
namespace Lax455465Proofs.PathRecordArithmetic
open AcyclicFlowDecomposition PathSimplification
variable {α : Type*} [Fintype α] [DecidableEq α]

def routed (rs : Records α) (s t : α) : ℚ :=
  (rs.map fun r => if r.1.head?=some s ∧ r.1.getLast?=some t then r.2 else 0).sum

@[simp] theorem routed_nil (s t : α) : routed [] s t=0 := rfl
@[simp] theorem routed_cons (r : List α×ℚ) (rs : Records α) (s t : α) :
    routed (r::rs) s t=(if r.1.head?=some s ∧ r.1.getLast?=some t then r.2 else 0)+routed rs s t := rfl

theorem load_append (rs ts : Records α) (u v : α) : load (rs++ts) u v=load rs u v+load ts u v := by
  simp [load]

theorem routed_append (rs ts : Records α) (s t : α) : routed (rs++ts) s t=routed rs s t+routed ts s t := by
  simp [routed]

theorem load_flatten (rs : List (Records α)) (u v : α) :
    load rs.flatten u v=(rs.map fun ts => load ts u v).sum := by
  induction rs with
  | nil => simp
  | cons r rs ih => simp [load_append,ih]

theorem routed_flatten (rs : List (Records α)) (s t : α) :
    routed rs.flatten s t=(rs.map fun ts => routed ts s t).sum := by
  induction rs with
  | nil => simp
  | cons r rs ih => simp [routed_append,ih]

theorem routed_valid {rs : Records α} {u v : α} (h : Valid u v rs) (s t : α) :
    routed rs s t=if u=s ∧ v=t then mass rs else 0 := by
  induction rs with
  | nil => simp
  | cons r rs ih =>
    have hr := h r (by simp)
    have ht : Valid u v rs := fun r' hr' => h r' (by simp [hr'])
    simp only [routed_cons,mass_cons,hr.2.1,hr.2.2.1,Option.some.injEq,ih ht]
    split_ifs <;> ring

theorem count_loop_zero {xs : List α} (h : xs.Nodup) (u : α) : PathCounting.count xs u u=0 := by
  rw [PathCounting.count_eq h]
  apply if_neg
  induction xs with
  | nil => simp
  | cons a xs ih =>
    cases xs with
    | nil => simp
    | cons b xs =>
      simp only [arcs_cons_cons,List.mem_cons,Prod.mk.injEq,not_or]
      refine ⟨?_,ih (List.nodup_cons.mp h).2⟩
      rintro ⟨rfl,rfl⟩
      exact (List.nodup_cons.mp h).1 (by simp)

theorem load_loop_zero (rs : Records α) (hn : ∀ r∈rs,r.1.Nodup) (u : α) : load rs u u=0 := by
  apply List.sum_eq_zero
  intro z hz
  obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hz
  rw [count_loop_zero (hn r hr),mul_zero]

end Lax455465Proofs.PathRecordArithmetic
