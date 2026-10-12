import Lax455465Proofs.RamMaskedMinimum
import Lax455465Proofs.RamRootDistances
import Lax455465Proofs.SetDistances

namespace Lax455465Proofs.SetDistanceData
open scoped NNRat

theorem valid_flags {n : ℕ} (S : Finset (Fin n)) (i : ℕ) (hi : i<n) :
    RamMaskedMinimum.valid (CutScoreData.vertexFlags S) i ↔ (⟨i,hi⟩ : Fin n)∈S := by
  by_cases hv : (⟨i,hi⟩ : Fin n)∈S <;>
    simp [RamMaskedMinimum.valid,CutScoreData.vertexFlags,MaskedMassData.flags,ResidualData.mask,hi,hv]

theorem mask_nonempty {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty) :
    ∃ i<n,RamMaskedMinimum.valid (CutScoreData.vertexFlags S) i := by
  obtain ⟨v,hv⟩ := hS
  exact ⟨v.val,v.isLt,(valid_flags S v.val v.isLt).mpr hv⟩

theorem minimum_eq_inf {n : ℕ} (f : Fin n → ℚ≥0) (S : Finset (Fin n)) (hS : S.Nonempty) :
    RamMaskedMinimum.minimum (List.ofFn f) (CutScoreData.vertexFlags S)=S.inf' hS f := by
  let valid := RamMaskedMinimum.valid (CutScoreData.vertexFlags S)
  let value := RamMaskedMinimum.value (List.ofFn f)
  have hvalue (v : Fin n) : value v.val=f v := by
    simp [value,RamMaskedMinimum.value]
  cases he : BestCutIndex.best valid value n with
  | none =>
    obtain ⟨i,hi,hv⟩ := mask_nonempty S hS
    exact False.elim ((BestCutIndex.best_none valid value n).mp he i hi hv)
  | some j =>
    have hs := BestCutIndex.best_sound valid value n j he
    have hjS : (⟨j,hs.1⟩ : Fin n)∈S := (valid_flags S j hs.1).mp hs.2
    simp only [RamMaskedMinimum.minimum,List.length_ofFn,show
      BestCutIndex.best (RamMaskedMinimum.valid (CutScoreData.vertexFlags S))
        (RamMaskedMinimum.value (List.ofFn f)) n=some j from he]
    change value j=S.inf' hS f
    apply le_antisymm
    · apply Finset.le_inf'
      intro v hv
      have h := BestCutIndex.best_minimal valid value n j v.val he v.isLt ((valid_flags S v.val v.isLt).mpr hv)
      rwa [hvalue v] at h
    · rw [hvalue ⟨j,hs.1⟩]
      exact Finset.inf'_le f hjS

def distance {n : ℕ} (toSet : Bool) (d : MetricMatrix.Matrix n) (S : Finset (Fin n))
    (hS : S.Nonempty) (v : Fin n) : ℚ≥0 := S.inf' hS fun u => if toSet then d v u else d u v

theorem minimum_vector {n : ℕ} (toSet : Bool) (d : MetricMatrix.Matrix n) (S : Finset (Fin n))
    (hS : S.Nonempty) (v : Fin n) :
    RamMaskedMinimum.minimum (RamRootDistances.vector toSet v d) (CutScoreData.vertexFlags S)=distance toSet d S hS v :=
  minimum_eq_inf _ S hS

theorem coe_distance {n : ℕ} (toSet : Bool) (d : MetricMatrix.Matrix n) (S : Finset (Fin n))
    (hS : S.Nonempty) (v : Fin n) : (distance toSet d S hS v : ℚ)=
      if toSet then SetDistances.toSet (MetricMatrix.rational d) S hS v
      else SetDistances.fromSet (MetricMatrix.rational d) S hS v := by
  let f : Fin n → ℚ≥0 := fun u => if toSet then d v u else d u v
  have hcoe : ((S.inf' hS f : ℚ≥0) : ℚ)=S.inf' hS (fun u => (f u : ℚ)) := by
    obtain ⟨j,hj,hmin⟩ := Finset.exists_mem_eq_inf' hS f
    rw [hmin]
    apply le_antisymm
    · apply Finset.le_inf'
      intro u hu
      exact NNRat.coe_le_coe.mpr (hmin ▸ Finset.inf'_le f hu)
    · exact Finset.inf'_le _ hj
  cases toSet <;> exact hcoe

theorem height {n : ℕ} (toSet : Bool) (d : MetricMatrix.Matrix n) (S : Finset (Fin n))
    (hS : S.Nonempty) (M : ℕ) (hd : ∀ u v,LpInputSize.Height M (d u v : ℚ)) (v : Fin n) :
    LpInputSize.Height M (distance toSet d S hS v : ℚ) := by
  obtain ⟨j,hj,hmin⟩ := Finset.exists_mem_eq_inf' hS (fun u => if toSet then d v u else d u v)
  unfold distance
  rw [hmin]
  cases toSet <;> exact hd _ _

end Lax455465Proofs.SetDistanceData
