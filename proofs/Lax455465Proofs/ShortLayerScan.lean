import Lax455465Proofs.ShortLayerSelection
import Lax455465Proofs.RamFind

namespace Lax455465Proofs.ShortLayerScan
open ShortLayerSelection

/-- Include the last layer as a successful fallback, so every valid scan
has a result even if the quantitative stopping test never succeeds. -/
def predicate (n : ℕ) (R : ℚ) (value : ℕ → ℚ) (i : ℕ) : Bool :=
  decide (good n R value (i+1) ∨ i+1=n-1)

theorem first_minimal (p : ℕ → Bool) (count i : ℕ) (h : RamFind.first p count=some i) :
    ∀ j < i,p j=false := by
  obtain ⟨_,k,hk,hki,hminimal⟩ := List.find?_eq_some_iff_getElem.mp h
  have hki' : k=i := by simpa using hki
  subst k
  intro j hj
  simpa using hminimal j hj

theorem selected (n : ℕ) (hn : 2 ≤ n) (R : ℚ) (value : ℕ → ℚ) :
    RamFind.first (predicate n R value) (n-1)=some (select n R value-1) := by
  have hsome : ∃ i,RamFind.first (predicate n R value) (n-1)=some i := by
    cases he : RamFind.first (predicate n R value) (n-1) with
    | some i => exact ⟨i,rfl⟩
    | none =>
      have hh := RamFind.first_none _ _ he (n-2) (by omega)
      have ht : predicate n R value (n-2)=true := by
        simp only [predicate,decide_eq_true_eq]
        exact Or.inr (by omega)
      rw [ht] at hh
      cases hh
  obtain ⟨i,hi⟩ := hsome
  obtain ⟨hib,hgood⟩ := RamFind.first_some _ _ _ hi
  have hstopping : good n R value (i+1) ∨ i+1=n-1 := by
    simpa only [predicate,decide_eq_true_eq] using hgood
  have hmin := first_minimal _ _ _ hi
  obtain ⟨hsel1,hselmax⟩ := select_range n hn R value
  have hle : select n R value ≤ i+1 := by
    rcases hstopping with hg | he
    · exact select_le n R value (i+1) (by omega) (fun _ => hg)
    · omega
  have hge : i+1 ≤ select n R value := by
    by_contra hh
    have hlt : select n R value-1 < i := by omega
    have hp := hmin _ hlt
    have htrue : predicate n R value (select n R value-1)=true := by
      simp only [predicate,decide_eq_true_eq]
      rw [Nat.sub_add_cancel hsel1]
      exact select_good_or_full n R value
    rw [htrue] at hp
    cases hp
  have he : select n R value-1=i := by omega
  rwa [he]

end Lax455465Proofs.ShortLayerScan
