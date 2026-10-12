import Lax455465.ShortPathFlow
import Mathlib.Data.List.TakeWhile
import Mathlib.Tactic

namespace Lax455465Proofs.PathSimplification
open List
variable {α : Type*} [DecidableEq α]

/-- Remove a prefix ending just before the first occurrence of `a`. -/
def suffixAt (a : α) (xs : List α) : List α := xs.dropWhile (fun b => decide (b ≠ a))

/-- Erase cycles from the tail backwards, retaining both endpoints and
only original directed arcs. This also removes waiting steps. -/
def simplify : List α → List α
  | [] => []
  | a::xs => let ys := simplify xs
    if a ∈ ys then suffixAt a ys else a::ys

def arcs (xs : List α) := xs.zip xs.tail

omit [DecidableEq α] in
@[simp] theorem arcs_nil : arcs ([] : List α) = [] := rfl
omit [DecidableEq α] in
@[simp] theorem arcs_singleton (a : α) : arcs [a] = [] := rfl
omit [DecidableEq α] in
@[simp] theorem arcs_cons_cons (a b : α) (xs : List α) :
    arcs (a::b::xs) = (a,b)::arcs (b::xs) := rfl

theorem from_sublist (a : α) (xs : List α) : suffixAt a xs <+ xs := List.dropWhile_sublist _

theorem from_head (a : α) (xs : List α) (ha : a ∈ xs) : (suffixAt a xs).head?=some a := by
  induction xs with
  | nil => cases ha
  | cons b xs ih =>
    by_cases he : b=a
    · subst b; simp [suffixAt]
    · have hx : a∈xs := by simpa [Ne.symm he] using ha
      simpa [suffixAt,he] using ih hx

theorem from_last (a : α) (xs : List α) (ha : a∈xs) : (suffixAt a xs).getLast?=xs.getLast? := by
  induction xs with
  | nil => cases ha
  | cons b xs ih =>
    by_cases he : b=a
    · subst b; simp [suffixAt]
    · have hx : a∈xs := by simpa [Ne.symm he] using ha
      have hs : suffixAt a (b::xs)=suffixAt a xs := by simp [suffixAt,he]
      rw [hs,ih hx,List.getLast?_cons_of_ne_nil (List.ne_nil_of_mem hx)]

theorem arcs_from_sublist (a : α) (xs : List α) : arcs (suffixAt a xs) <+ arcs xs := by
  induction xs with
  | nil => simp [suffixAt]
  | cons b xs ih =>
    by_cases he : b=a
    · subst b; simp [suffixAt]
    · have hs : suffixAt a (b::xs)=suffixAt a xs := by simp [suffixAt,he]
      rw [hs]
      exact ih.trans (by cases xs <;> simp)

theorem sublist (xs : List α) : simplify xs <+ xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [simplify]
    split_ifs with h
    · exact ((from_sublist a (simplify xs)).trans ih).cons a
    · exact ih.cons_cons a

theorem nodup (xs : List α) : (simplify xs).Nodup := by
  induction xs with
  | nil => simp [simplify]
  | cons a xs ih =>
    simp only [simplify]
    split_ifs with h
    · exact ih.sublist (from_sublist a (simplify xs))
    · exact List.nodup_cons.mpr ⟨h,ih⟩

@[simp] theorem head (xs : List α) : (simplify xs).head?=xs.head? := by
  cases xs with
  | nil => rfl
  | cons a xs =>
    simp only [simplify,List.head?_cons]
    split_ifs with h
    · exact from_head a _ h
    · rfl

@[simp] theorem eq_nil (xs : List α) : simplify xs=[] ↔ xs=[] := by
  constructor
  · intro h
    have hh := head xs
    rw [h] at hh
    cases xs <;> simp_all
  · intro h; subst xs; rfl

@[simp] theorem last (xs : List α) : (simplify xs).getLast?=xs.getLast? := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [simplify]
    split_ifs with h
    · rw [from_last a _ h,ih]
      have hne : xs ≠ [] := by intro he; subst xs; simp [simplify] at h
      cases xs with
      | nil => exact (hne rfl).elim
      | cons b xs => rfl
    · cases xs with
      | nil => rfl
      | cons b xs =>
        have hne : simplify (b::xs) ≠ [] := by simp
        cases hy : simplify (b::xs) with
        | nil => exact (hne hy).elim
        | cons c ys =>
          simpa only [hy,List.getLast?_cons_cons] using ih

theorem arcs_sublist (xs : List α) : arcs (simplify xs) <+ arcs xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [simplify]
    split_ifs with h
    · exact ((arcs_from_sublist a (simplify xs)).trans ih).trans (by cases xs <;> simp)
    · cases xs with
      | nil => rfl
      | cons b xs =>
        have hh := head (b::xs)
        cases hy : simplify (b::xs) with
        | nil => simp [hy] at hh
        | cons c ys =>
          have hc : c=b := by simpa [hy] using hh
          subst c
          simp only [hy,arcs_cons_cons] at ih ⊢
          exact ih.cons_cons (a,b)

theorem length_le (xs : List α) : (simplify xs).length ≤ xs.length := (sublist xs).length_le

theorem arc_count_le (xs : List α) (a b : α) :
    (arcs (simplify xs)).count (a,b) ≤ (arcs xs).count (a,b) :=
  (arcs_sublist xs).count_le _

theorem length_le_card [Fintype α] (xs : List α) :
    (simplify xs).length ≤ Fintype.card α := (nodup xs).length_le_card

/-- Distinct endpoints survive simplification, so the resulting record has
at least one edge and is a valid simple path. -/
theorem distinct_endpoints {xs : List α} {s t : α} (hne : s ≠ t)
    (hs : xs.head?=some s) (ht : xs.getLast?=some t) :
    2 ≤ (simplify xs).length ∧ (simplify xs).Nodup ∧
      (simplify xs).head?=some s ∧ (simplify xs).getLast?=some t := by
  have hh := (head xs).trans hs
  have hl := (last xs).trans ht
  refine ⟨?_,nodup xs,hh,hl⟩
  cases he : simplify xs with
  | nil => simp [he] at hh
  | cons a ys =>
    cases ys with
    | nil => simp only [he,List.head?_cons,Option.some.injEq] at hh
             simp only [he,List.getLast?_singleton,Option.some.injEq] at hl
             exact (hne (hh.symm.trans hl)).elim
    | cons b ys => simp

#guard simplify ([0,1,2,1,3] : List ℕ) == [0,1,3]
#guard simplify ([0,0,1,2,1,1,3,3] : List ℕ) == [0,1,3]
#guard simplify ([0,1,0] : List ℕ) == [0]

end Lax455465Proofs.PathSimplification
