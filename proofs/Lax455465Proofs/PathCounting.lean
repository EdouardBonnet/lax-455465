import Lax455465Proofs.PathSimplification

open scoped BigOperators
namespace Lax455465Proofs.PathCounting
open PathSimplification
variable {α : Type*} [Fintype α] [DecidableEq α]

def count (xs : List α) (u v : α) : ℚ := (arcs xs).count (u,v)

@[simp] theorem count_nil (u v : α) : count [] u v=0 := rfl
@[simp] theorem count_singleton (a u v : α) : count [a] u v=0 := rfl

theorem count_cons_cons (a b u v : α) (xs : List α) :
    count (a::b::xs) u v=count (b::xs) u v+(if a=u ∧ b=v then 1 else 0) := by
  simp only [count,arcs_cons_cons,List.count_cons,Nat.cast_add]
  by_cases he : a=u ∧ b=v
  · rcases he with ⟨rfl,rfl⟩
    simp
  · have hh : (u,v) ≠ (a,b) := by simpa [Prod.mk.injEq,eq_comm] using he
    simp [he,hh]

theorem arcs_nodup {xs : List α} (h : xs.Nodup) : (arcs xs).Nodup := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    cases xs with
    | nil => simp
    | cons b xs =>
      rw [arcs_cons_cons,List.nodup_cons]
      refine ⟨?_,ih (List.nodup_cons.mp h).2⟩
      intro he
      exact (List.nodup_cons.mp h).1 (List.of_mem_zip he).1

theorem count_eq {xs : List α} (h : xs.Nodup) (u v : α) :
    count xs u v=if (u,v)∈arcs xs then 1 else 0 := by
  simp only [count,(arcs_nodup h).count]
  split_ifs <;> norm_num

theorem nonnegative (xs : List α) (u v : α) : 0 ≤ count xs u v := by unfold count; positivity

/-- The net unit flow through every internal vertex cancels. -/
theorem balance {xs : List α} {s t : α} (hs : xs.head?=some s)
    (ht : xs.getLast?=some t) (u : α) :
    (∑ v,count xs u v)-(∑ v,count xs v u)=
      (if u=s then 1 else 0)-(if u=t then 1 else 0) := by
  induction xs generalizing s with
  | nil => simp at hs
  | cons a xs ih =>
    have ha : a=s := by simpa using hs
    subst a
    cases xs with
    | nil =>
      have hst : s=t := by simpa using ht
      subst t
      simp
    | cons b xs =>
      have hh := ih rfl (by simpa using ht)
      simp only [count_cons_cons,Finset.sum_add_distrib]
      have hsum₁ : (∑ v : α,if s=u ∧ b=v then (1 : ℚ) else 0)=if u=s then 1 else 0 := by
        by_cases he : u=s
        · subst u; simp
        · simp [he,Ne.symm he]
      have hsum₂ : (∑ v : α,if s=v ∧ b=u then (1 : ℚ) else 0)=if u=b then 1 else 0 := by
        by_cases he : u=b
        · subst u; simp
        · simp [he,Ne.symm he]
      rw [hsum₁,hsum₂]
      linarith

theorem first_edge {xs : List α} {s t : α} (hs : xs.head?=some s)
    (ht : xs.getLast?=some t) (hst : s ≠ t) : ∃ v,(s,v)∈arcs xs := by
  cases xs with
  | nil => simp at hs
  | cons u xs =>
    have he : u=s := by simpa using hs
    subst u
    cases xs with
    | nil => simp at ht; exact (hst ht).elim
    | cons v xs => exact ⟨v,by simp⟩

end Lax455465Proofs.PathCounting
