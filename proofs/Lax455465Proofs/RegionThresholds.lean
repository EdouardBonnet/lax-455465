import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.GetD
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

namespace Lax455465Proofs.RegionThresholds

/-- Candidate radii in a grid cell: both endpoints and all inward/outward
vertex-distance events lying in the cell. This is an exact rational list. -/
def events {n : ℕ} (outDistance inDistance : Fin n → ℚ) (a b : ℚ) : Finset ℚ :=
  insert a (insert b ((Finset.univ.image outDistance ∪ Finset.univ.image inDistance).filter
    (fun r => a ≤ r ∧ r ≤ b)))

def candidates {n : ℕ} (outDistance inDistance : Fin n → ℚ) (a b : ℚ) : List ℚ :=
  (events outDistance inDistance a b).sort

theorem left_mem {n : ℕ} (outDistance inDistance : Fin n → ℚ) (a b : ℚ) :
    a ∈ events outDistance inDistance a b := by simp [events]

theorem right_mem {n : ℕ} (outDistance inDistance : Fin n → ℚ) (a b : ℚ) :
    b ∈ events outDistance inDistance a b := by simp [events]

theorem bounds {n : ℕ} (outDistance inDistance : Fin n → ℚ) (a b : ℚ) (hab : a ≤ b) :
    ∀ r ∈ events outDistance inDistance a b, a ≤ r ∧ r ≤ b := by
  intro r hr
  simp only [events, Finset.mem_insert, Finset.mem_filter] at hr
  rcases hr with rfl | rfl | ⟨_, h⟩
  · exact ⟨le_rfl, hab⟩
  · exact ⟨hab, le_rfl⟩
  · exact h

/-- A cell has at most 2n+2 candidate radii, irrespective of coefficient size. -/
theorem length_bound {n : ℕ} (outDistance inDistance : Fin n → ℚ) (a b : ℚ) :
    (candidates outDistance inDistance a b).length ≤ 2 * n + 2 := by
  unfold candidates
  rw [Finset.length_sort]
  have hout : (Finset.univ.image outDistance).card ≤ n := by
    simpa using (Finset.card_image_le (s := Finset.univ) (f := outDistance))
  have hin : (Finset.univ.image inDistance).card ≤ n := by
    simpa using (Finset.card_image_le (s := Finset.univ) (f := inDistance))
  have hunion := Finset.card_union_le (Finset.univ.image outDistance) (Finset.univ.image inDistance)
  have hfilter := Finset.card_filter_le
    (s := Finset.univ.image outDistance ∪ Finset.univ.image inDistance)
    (p := fun r => a ≤ r ∧ r ≤ b)
  have hright := Finset.card_insert_le b
    ((Finset.univ.image outDistance ∪ Finset.univ.image inDistance).filter (fun r => a ≤ r ∧ r ≤ b))
  have hleft := Finset.card_insert_le a (insert b
    ((Finset.univ.image outDistance ∪ Finset.univ.image inDistance).filter (fun r => a ≤ r ∧ r ≤ b)))
  unfold events
  omega

/-- Consecutive members of the sorted finite set leave no member between them. -/
private theorem no_member_between (s : Finset ℚ) (j : ℕ) (hj : j + 1 < s.sort.length)
    (r : ℚ) (hr : r ∈ s) :
    ¬ (s.sort.get ⟨j, by omega⟩ < r ∧ r < s.sort.get ⟨j + 1, hj⟩) := by
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp ((Finset.mem_sort (· ≤ ·)).mpr hr)
  have hmono := (Finset.sortedLT_sort s).monotone
  rintro ⟨hlow, hhigh⟩
  by_cases hle : i.val ≤ j
  · have h := hmono (show i ≤ ⟨j, by omega⟩ from hle)
    rw [hi] at h
    exact (not_lt_of_ge h) hlow
  · have h := hmono (show (⟨j + 1, hj⟩ : Fin s.sort.length) ≤ i by
      change j + 1 ≤ i.val
      omega)
    rw [hi] at h
    exact (not_lt_of_ge h) hhigh

/-- No inward or outward vertex-distance event lies strictly between
consecutive tested radii. This discharges the volume-growth hypotheses. -/
theorem no_event {n : ℕ} (outDistance inDistance : Fin n → ℚ) (a b : ℚ)
    (hab : a ≤ b) (j : ℕ) (hj : j + 1 < (candidates outDistance inDistance a b).length) :
    (∀ v, ¬ ((candidates outDistance inDistance a b).get ⟨j, by omega⟩ < outDistance v ∧
      outDistance v < (candidates outDistance inDistance a b).get ⟨j + 1, hj⟩)) ∧
    (∀ v, ¬ ((candidates outDistance inDistance a b).get ⟨j, by omega⟩ < inDistance v ∧
      inDistance v < (candidates outDistance inDistance a b).get ⟨j + 1, hj⟩)) := by
  change j + 1 < (events outDistance inDistance a b).sort.length at hj
  have hstart := (bounds outDistance inDistance a b hab _
    ((Finset.mem_sort (· ≤ ·)).mp (List.get_mem _ ⟨j, by omega⟩))).1
  have hend := (bounds outDistance inDistance a b hab _
    ((Finset.mem_sort (· ≤ ·)).mp (List.get_mem _ ⟨j + 1, hj⟩))).2
  constructor
  · intro v h
    apply no_member_between (events outDistance inDistance a b) j hj (outDistance v) ?_ h
    simp only [events, Finset.mem_insert, Finset.mem_filter]
    right; right
    exact ⟨Finset.mem_union_left _ (Finset.mem_image.mpr ⟨v, Finset.mem_univ _, rfl⟩),
      ⟨hstart.trans h.1.le, h.2.le.trans hend⟩⟩
  · intro v h
    apply no_member_between (events outDistance inDistance a b) j hj (inDistance v) ?_ h
    simp only [events, Finset.mem_insert, Finset.mem_filter]
    right; right
    exact ⟨Finset.mem_union_right _ (Finset.mem_image.mpr ⟨v, Finset.mem_univ _, rfl⟩),
      ⟨hstart.trans h.1.le, h.2.le.trans hend⟩⟩


/-- Natural indexing of the event list, used by the finite grid-cell loop. -/
def radius {n : ℕ} (outDistance inDistance : Fin n → ℚ) (a b : ℚ) (i : ℕ) : ℚ :=
  (candidates outDistance inDistance a b).getD i b

theorem length_pos {n : ℕ} (outDistance inDistance : Fin n → ℚ) (a b : ℚ) :
    0 < (candidates outDistance inDistance a b).length := by
  unfold candidates
  rw [Finset.length_sort]
  exact Finset.card_pos.mpr ⟨a, left_mem outDistance inDistance a b⟩

theorem radius_eq_get {n : ℕ} (outDistance inDistance : Fin n → ℚ) (a b : ℚ)
    (i : Fin (candidates outDistance inDistance a b).length) :
    radius outDistance inDistance a b i.val =
      (candidates outDistance inDistance a b).get i :=
  List.getD_eq_get _ _ i

theorem radius_first {n : ℕ} (outDistance inDistance : Fin n → ℚ) (a b : ℚ) (hab : a ≤ b) :
    radius outDistance inDistance a b 0 = a := by
  let i : Fin (candidates outDistance inDistance a b).length :=
    ⟨0, length_pos outDistance inDistance a b⟩
  change radius outDistance inDistance a b i.val = a
  rw [radius_eq_get]
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp
    ((Finset.mem_sort (· ≤ ·)).mpr (left_mem outDistance inDistance a b))
  apply le_antisymm
  · have h := (Finset.sortedLT_sort (events outDistance inDistance a b)).monotone
      (show i ≤ j by exact Nat.zero_le _)
    exact h.trans_eq hj
  · exact (bounds outDistance inDistance a b hab _
      ((Finset.mem_sort (· ≤ ·)).mp (List.get_mem _ i))).1

theorem radius_last {n : ℕ} (outDistance inDistance : Fin n → ℚ) (a b : ℚ) (hab : a ≤ b) :
    radius outDistance inDistance a b ((candidates outDistance inDistance a b).length - 1) = b := by
  have hpos := length_pos outDistance inDistance a b
  let i : Fin (candidates outDistance inDistance a b).length :=
    ⟨(candidates outDistance inDistance a b).length - 1, by omega⟩
  change radius outDistance inDistance a b i.val = b
  rw [radius_eq_get]
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp
    ((Finset.mem_sort (· ≤ ·)).mpr (right_mem outDistance inDistance a b))
  apply le_antisymm
  · exact (bounds outDistance inDistance a b hab _
      ((Finset.mem_sort (· ≤ ·)).mp (List.get_mem _ i))).2
  · have h := (Finset.sortedLT_sort (events outDistance inDistance a b)).monotone
      (show j ≤ i by change j.val ≤ _; exact Nat.le_sub_one_of_lt j.isLt)
    exact (le_of_eq hj.symm).trans h

theorem radius_monotone {n : ℕ} (outDistance inDistance : Fin n → ℚ) (a b : ℚ)
    (j : ℕ) (hj : j + 1 < (candidates outDistance inDistance a b).length) :
    radius outDistance inDistance a b j ≤ radius outDistance inDistance a b (j + 1) := by
  rw [radius_eq_get outDistance inDistance a b ⟨j, by omega⟩,
    radius_eq_get outDistance inDistance a b ⟨j + 1, hj⟩]
  exact (Finset.sortedLT_sort _).monotone (show (⟨j, by omega⟩ : Fin _) ≤ ⟨j + 1, hj⟩ by
    change j ≤ j + 1
    omega)

end Lax455465Proofs.RegionThresholds
