import Lax455465Proofs.PathSimplification

namespace Lax455465Proofs.LoopErasure
open PathSimplification List
variable {α : Type*} [DecidableEq α]

/-- Maintain a simple stack while reading a walk from left to right.
Revisiting a vertex truncates the stack at that vertex. -/
def append (xs : List α) (v : α) : List α :=
  if v∈xs then xs.take (xs.idxOf v+1) else xs++[v]

theorem nodup {xs : List α} (h : xs.Nodup) (v : α) : (append xs v).Nodup := by
  unfold append
  split_ifs with hv
  · exact h.take
  · simpa using h.concat hv

theorem length (xs : List α) (v : α) : (append xs v).length≤xs.length+1 := by
  unfold append
  split_ifs <;> simp only [List.length_take,List.length_append,List.length_singleton] <;> omega

theorem last (xs : List α) (v : α) : (append xs v).getLast?=some v := by
  unfold append
  split_ifs with hv
  · have hi := List.idxOf_lt_length_of_mem hv
    rw [List.take_succ_eq_append_getElem hi]
    simp only [List.getLast?_append,List.getLast?_singleton,Option.or_some]
    rw [List.getElem_idxOf hi]
    rfl
  · simp

theorem head (xs : List α) (v : α) (hx : xs≠[]) : (append xs v).head?=xs.head? := by
  unfold append
  split_ifs with hv
  · cases xs with
    | nil => cases hx rfl
    | cons a xs => simp
  · cases xs with
    | nil => cases hx rfl
    | cons a xs => simp

theorem arcs_take (xs : List α) (k : ℕ) : arcs (xs.take k)=(arcs xs).take (k-1) := by
  induction k generalizing xs with
  | zero => simp [arcs]
  | succ k ih =>
    cases xs with
    | nil => simp [arcs]
    | cons a xs =>
      cases k with
      | zero => simp [arcs]
      | succ k =>
        cases xs with
        | nil => simp [arcs]
        | cons b xs =>
          simpa only [List.take_succ_cons,arcs_cons_cons,Nat.add_sub_cancel,List.take_succ_cons] using
            congrArg (List.cons (a,b)) (ih (b::xs))

theorem arcs_append (xs : List α) (v : α) (u : α) (hlast : xs.getLast?=some u) :
    arcs (xs++[v])=arcs xs++[(u,v)] := by
  induction xs with
  | nil => simp at hlast
  | cons a xs ih =>
    cases xs with
    | nil => simp only [List.getLast?_singleton,Option.some.injEq] at hlast
             subst a
             rfl
    | cons b xs =>
      simp only [List.getLast?_cons_cons] at hlast
      change (a,b)::arcs ((b::xs)++[v])=(a,b)::(arcs (b::xs)++[(u,v)])
      rw [ih hlast]

/-- Updating the simple stack adds only the current walk edge or discards
a suffix. Thus no capacity-consuming arc is introduced by cycle erasure. -/
theorem arcs_sublist (xs ys : List α) (u v : α)
    (hx : xs.getLast?=some u) (hy : ys.getLast?=some u)
    (h : arcs ys <+ arcs xs) : arcs (append ys v) <+ arcs (xs++[v]) := by
  unfold append
  rw [arcs_append xs v u hx]
  split_ifs with hv
  · rw [arcs_take]
    exact ((List.take_sublist _ _).trans h).trans (List.sublist_append_left _ _)
  · rw [arcs_append ys v u hy]
    exact h.append_right [(u,v)]

#guard append ([0,1,2] : List ℕ) 1 == [0,1]
#guard append ([0,1,2] : List ℕ) 3 == [0,1,2,3]
#guard append ([0] : List ℕ) 0 == [0]

end Lax455465Proofs.LoopErasure
