import Lax455465Proofs.PathCounting

open scoped BigOperators
namespace Lax455465Proofs.RealPathCounting
open PathSimplification
variable {α : Type*} [Fintype α] [DecidableEq α]

def count (xs : List α) (u v : α) : ℝ := (arcs xs).count (u,v)

omit [Fintype α] in
@[simp] theorem count_nil (u v : α) : count [] u v = 0 := by simp [count]

theorem count_eq {xs : List α} (h : xs.Nodup) (u v : α) :
    count xs u v = if (u,v) ∈ arcs xs then 1 else 0 := by
  simp only [count, (PathCounting.arcs_nodup h).count]
  split_ifs <;> norm_num

omit [Fintype α] in
theorem nonnegative (xs : List α) (u v : α) : 0 ≤ count xs u v := by
  unfold count
  positivity

theorem balance {xs : List α} {s t : α} (hs : xs.head? = some s)
    (ht : xs.getLast? = some t) (u : α) :
    (∑ v, count xs u v) - (∑ v, count xs v u) =
      (if u = s then 1 else 0) - (if u = t then 1 else 0) := by
  have h := congrArg (fun q : ℚ => (q : ℝ)) (PathCounting.balance hs ht u)
  simpa only [PathCounting.count, Rat.cast_sub, Rat.cast_sum, Rat.cast_natCast,
    apply_ite, Rat.cast_one, Rat.cast_zero, count] using h

end Lax455465Proofs.RealPathCounting
