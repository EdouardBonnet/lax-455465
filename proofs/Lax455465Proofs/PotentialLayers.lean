import Lax455465Proofs.ThresholdRounding
import Mathlib.Data.List.Sort
import Mathlib.Data.List.GetD

open scoped BigOperators

namespace Lax455465Proofs.PotentialLayers

open CutLayers

/-- Sorted rational values, retaining repetitions. -/
def values {n : ℕ} (a : Fin n → ℚ) : List ℚ :=
  (List.ofFn a).mergeSort (· ≤ ·)

theorem values_length {n : ℕ} (a : Fin n → ℚ) : (values a).length = n := by
  simp [values]

theorem value_mem {n : ℕ} (a : Fin n → ℚ) (v : Fin n) : a v ∈ values a := by
  exact List.mem_mergeSort.mpr (List.mem_ofFn.mpr ⟨v, rfl⟩)

/-- The last value is repeated after the end, making the last gap zero. -/
def level (xs : List ℚ) (i : ℕ) : ℚ := xs.getD (min i (xs.length - 1)) 0

theorem level_monotone (xs : List ℚ) (hs : xs.SortedLE) : Monotone (level xs) := by
  intro i j hij
  cases xs with
  | nil => simp [level]
  | cons x xs =>
    have hi : min i ((x :: xs).length - 1) < (x :: xs).length := by
      simp only [List.length_cons]
      omega
    have hj : min j ((x :: xs).length - 1) < (x :: xs).length := by
      simp only [List.length_cons]
      omega
    unfold level
    rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj]
    exact hs.monotone_get (min_le_min_right _ hij)

def rank {n : ℕ} (a : Fin n → ℚ) (v : Fin n) : Fin (n + 1) :=
  ⟨(values a).idxOf (a v), by
    have h := List.idxOf_lt_length_of_mem (value_mem a v)
    rw [values_length] at h
    omega⟩

theorem level_rank {n : ℕ} (a : Fin n → ℚ) (v : Fin n) :
    level (values a) (rank a v).val = a v := by
  have h := List.idxOf_lt_length_of_mem (value_mem a v)
  have hle : (values a).idxOf (a v) ≤ (values a).length - 1 := by omega
  unfold level rank
  rw [min_eq_left hle, List.getD_eq_getElem _ _ h]
  exact List.getElem_idxOf h

/-- Sort, locate each vertex, and take adjacent differences. -/
def build {n : ℕ} (a : Fin n → ℚ) : Layers n n where
  rank := rank a
  gap i := level (values a) i.succ.val - level (values a) i.castSucc.val
  gap_nonneg i := sub_nonneg.mpr
    (level_monotone _ List.sortedLE_mergeSort (by simp))

private theorem prefix_step {k : ℕ} (f : Fin k → ℚ) (r : Fin k) :
    (∑ i : Fin k, if i.val < r.succ.val then f i else 0) =
      (∑ i : Fin k, if i.val < r.castSucc.val then f i else 0) + f r := by
  have hterm : ∀ i : Fin k,
      (if i.val < r.succ.val then f i else 0) =
        (if i.val < r.castSucc.val then f i else 0) + (if i = r then f i else 0) := by
    intro i
    by_cases hir : i = r
    · subst i
      simp
    · have hval : i.val ≠ r.val := fun h => hir (Fin.ext h)
      simp only [Fin.val_succ, Fin.val_castSucc, if_neg hir, add_zero]
      have hpred : i.val < r.val + 1 ↔ i.val < r.val := by omega
      simp only [hpred]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib]
  simp

/-- Exact telescoping for a retained finite rank. -/
theorem telescope {k : ℕ} (a : Fin (k + 1) → ℚ) (r : Fin (k + 1)) :
    (∑ i : Fin k, if i.val < r.val then a i.succ - a i.castSucc else 0) = a r - a 0 := by
  refine Fin.induction ?_ ?_ r
  · simp
  · intro i ih
    rw [prefix_step, ih]
    ring

/-- Sorting changes only an additive constant, so every difference is preserved. -/
theorem potential_eq {n : ℕ} (a : Fin n → ℚ) (v : Fin n) :
    potential (build a) v = a v - level (values a) 0 := by
  change (∑ i : Fin n, if i.val < (rank a v).val then
    level (values a) i.succ.val - level (values a) i.castSucc.val else 0) = _
  rw [telescope (fun i : Fin (n + 1) => level (values a) i.val) (rank a v), level_rank]
  rfl

theorem difference_eq {n : ℕ} (a : Fin n → ℚ) (u v : Fin n) :
    potential (build a) v - potential (build a) u = a v - a u := by
  rw [potential_eq, potential_eq]
  ring

open Lax455465.RationalEncoding CutSweeps

/-- Separation of an arbitrary computed rational potential. -/
def separation {n : ℕ} (I : RationalInstance n) (a : Fin n → ℚ) : ℚ :=
  ∑ u, ∑ v, (I.weight u : ℚ) * I.weight v * max (a v - a u) 0

def edgeCost {n : ℕ} (I : RationalInstance n) (a : Fin n → ℚ) : ℚ :=
  ∑ u, ∑ v, (I.capacity u v : ℚ) * max (a v - a u) 0

private theorem separation_build {n : ℕ} (I : RationalInstance n) (a : Fin n → ℚ) :
    ThresholdRounding.separation I (build a) = separation I a := by
  simp only [ThresholdRounding.separation, separation, difference_eq]

private theorem edgeCost_build {n : ℕ} (I : RationalInstance n) (a : Fin n → ℚ) :
    ThresholdRounding.edgeCost I (build a) = edgeCost I a := by
  simp only [ThresholdRounding.edgeCost, edgeCost, difference_eq]

/-- Deterministic sweep of any rational potential, including ties and negative values. -/
def round {n : ℕ} (I : RationalInstance n) (a : Fin n → ℚ) : Option (Finset (Fin n)) :=
  ThresholdRounding.round I (build a)

theorem round_spec {n : ℕ} (I : RationalInstance n) (a : Fin n → ℚ)
    (hsep : 0 < separation I a) :
    ∃ S, round I a = some S ∧ admissibleQ I S ∧ ratioQ I S ≤ edgeCost I a / separation I a := by
  simpa only [round, separation_build, edgeCost_build] using
    ThresholdRounding.round_spec I (build a) (by simpa only [separation_build] using hsep)

theorem edgeCost_le {n : ℕ} (I : RationalInstance n) (a : Fin n → ℚ)
    (length : Fin n → Fin n → ℚ) (hnonneg : ∀ u v, 0 ≤ length u v)
    (hlip : ∀ u v, a v - a u ≤ length u v) :
    edgeCost I a ≤ ∑ u, ∑ v, (I.capacity u v : ℚ) * length u v := by
  rw [← edgeCost_build]
  exact ThresholdRounding.edgeCost_le I (build a) length hnonneg
    (by simpa only [difference_eq] using hlip)

end Lax455465Proofs.PotentialLayers
