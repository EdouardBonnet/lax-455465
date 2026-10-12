import Lax455465Proofs.ResidualLattice

namespace Lax455465Proofs.Bottleneck
open scoped NNRat

def minimum (a : ℚ≥0) (qs : List ℚ≥0) : ℚ≥0 := qs.foldl min a

@[simp] theorem minimum_nil (a : ℚ≥0) : minimum a []=a := rfl
@[simp] theorem minimum_cons (a q : ℚ≥0) (qs : List ℚ≥0) :
    minimum a (q::qs)=minimum (min a q) qs := rfl

theorem append (a : ℚ≥0) (qs rs : List ℚ≥0) :
    minimum a (qs++rs)=minimum (minimum a qs) rs := List.foldl_append

theorem selected (a : ℚ≥0) (qs : List ℚ≥0) : minimum a qs=a ∨ minimum a qs∈qs := by
  induction qs generalizing a with
  | nil => exact Or.inl rfl
  | cons q qs ih =>
    rcases ih (min a q) with he | he
    · by_cases h : a≤q
      · exact Or.inl (he.trans (min_eq_left h))
      · exact Or.inr (by rw [minimum_cons,he,min_eq_right (le_of_not_ge h)]; exact List.mem_cons_self)
    · exact Or.inr (List.mem_cons_of_mem q he)

theorem le_start (a : ℚ≥0) (qs : List ℚ≥0) : minimum a qs≤a := by
  induction qs generalizing a with
  | nil => rfl
  | cons q qs ih => exact (ih (min a q)).trans (min_le_left _ _)

theorem le_entry (a : ℚ≥0) (qs : List ℚ≥0) (q : ℚ≥0) (hq : q∈qs) : minimum a qs≤q := by
  induction qs generalizing a with
  | nil => cases hq
  | cons r qs ih =>
    rcases List.mem_cons.mp hq with rfl | hq
    · exact (le_start (min a q) qs).trans (min_le_right _ _)
    · exact ih (min a r) hq

theorem positive (a : ℚ≥0) (qs : List ℚ≥0) (ha : 0<a) (hq : ∀ q∈qs,0<q) : 0<minimum a qs := by
  rcases selected a qs with he | he
  · rwa [he]
  · exact hq _ he

theorem lattice (D H : ℕ) (a : ℚ≥0) (qs : List ℚ≥0)
    (ha : ResidualLattice.Bounded D H a) (hq : ∀ q∈qs,ResidualLattice.Bounded D H q) :
    ResidualLattice.Bounded D H (minimum a qs) := by
  rcases selected a qs with he | he
  · rwa [he]
  · exact hq _ he

theorem height (M : ℕ) (a : ℚ≥0) (qs : List ℚ≥0)
    (ha : a.num≤M ∧ a.den≤M) (hq : ∀ q∈qs,q.num≤M ∧ q.den≤M) :
    (minimum a qs).num≤M ∧ (minimum a qs).den≤M := by
  rcases selected a qs with he | he
  · rwa [he]
  · exact hq _ he

end Lax455465Proofs.Bottleneck
