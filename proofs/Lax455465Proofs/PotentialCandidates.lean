import Lax455465Proofs.PotentialLayers

namespace Lax455465Proofs.PotentialCandidates
open PotentialLayers

/-- A sorted layer, including one inside a run of equal values, is exactly
the nonstrict threshold shore of its actual potential value. -/
theorem layer_shore {n : ℕ} (a : Fin n → ℚ) (i : Fin n) :
    CutLayers.shore (build a) i=Finset.univ.filter (fun v => a v≤(values a)[i.val]'(by simpa [values_length] using i.isLt)) := by
  let xs := values a
  have hi : i.val<xs.length := by simpa only [xs,values_length] using i.isLt
  ext v
  simp only [CutLayers.shore,Finset.mem_filter,Finset.mem_univ,true_and]
  have hv : xs.idxOf (a v)<xs.length := List.idxOf_lt_length_of_mem (value_mem a v)
  have sorted : xs.SortedLE := List.sortedLE_mergeSort
  change xs.idxOf (a v) ≤ i.val ↔ a v ≤ xs[i.val]
  constructor
  · intro h
    have hm := sorted.monotone_get (show (⟨xs.idxOf (a v),hv⟩ : Fin xs.length)≤⟨i.val,hi⟩ from h)
    simpa only [List.get_eq_getElem,List.getElem_idxOf] using hm
  · intro h
    by_contra hn
    have hlt : i.val<xs.idxOf (a v) := by omega
    have hm := sorted.monotone_get (show (⟨i.val,hi⟩ : Fin xs.length)≤⟨xs.idxOf (a v),hv⟩ from hlt.le)
    have hrev : xs[i.val]≤a v := by simpa only [List.get_eq_getElem,List.getElem_idxOf] using hm
    have he : xs[i.val]=a v := le_antisymm hrev h
    have hnot := List.not_of_lt_findIdx (p := fun q : ℚ => q==a v) (xs := xs) hlt
    simp [he] at hnot

theorem layer_mem {n : ℕ} (a : Fin n → ℚ) (i : Fin n) :
    CutLayers.shore (build a) i∈CutSweeps.candidates a := by
  have hi : i.val<(values a).length := by simpa only [values_length] using i.isLt
  have hm : (values a)[i.val]∈values a := List.getElem_mem hi
  obtain ⟨v,hv⟩ := List.mem_ofFn.mp (List.mem_mergeSort.mp hm)
  rw [layer_shore,←hv]
  exact List.mem_map.mpr ⟨v,List.mem_finRange _,rfl⟩

theorem round_mem {n : ℕ} (I : Lax455465.RationalEncoding.RationalInstance n) (a : Fin n → ℚ)
    (S : Finset (Fin n)) (hS : PotentialLayers.round I a=some S) : S∈CutSweeps.candidates a := by
  have hm := (CutSweeps.choose_sound I (ThresholdRounding.layerCandidates (build a)) S hS).1
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hm
  exact layer_mem a i

end Lax455465Proofs.PotentialCandidates
