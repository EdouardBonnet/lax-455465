import Lax455465Proofs.RamThresholdMask
import Lax455465Proofs.CutScoreData

namespace Lax455465Proofs.ThresholdCutData
open Lax455465.RationalEncoding
open scoped NNRat

def potential {n : ℕ} (reversed : Bool) (values : Fin n → ℚ≥0) : Fin n → ℚ :=
  fun v => if reversed then -(values v : ℚ) else (values v : ℚ)
def shore {n : ℕ} (reversed : Bool) (values : Fin n → ℚ≥0) (threshold : ℚ≥0) : Finset (Fin n) :=
  Finset.univ.filter fun v => RamThresholdMask.chosen reversed (values v) threshold

def candidates {n : ℕ} (reversed : Bool) (values : Fin n → ℚ≥0) : List (Finset (Fin n)) :=
  (List.finRange n).map fun v => shore reversed values (values v)

theorem mask_eq {n : ℕ} (reversed : Bool) (values : Fin n → ℚ≥0) (threshold : ℚ≥0) :
    MaskedMassData.flags (fun v => RamThresholdMask.chosen reversed (values v) threshold)=
      CutScoreData.vertexFlags (shore reversed values threshold) := by
  unfold CutScoreData.vertexFlags
  congr 1
  funext v
  simp [shore,ResidualData.mask]

theorem candidates_eq {n : ℕ} (reversed : Bool) (values : Fin n → ℚ≥0) :
    candidates reversed values=CutSweeps.candidates (potential reversed values) := by
  apply List.map_congr_left
  intro v hv
  ext u
  cases reversed <;> simp [shore,potential,RamThresholdMask.chosen]

@[simp] theorem length_candidates {n : ℕ} (reversed : Bool) (values : Fin n → ℚ≥0) :
    (candidates reversed values).length=n := by simp [candidates]

def candidate {n : ℕ} (reversed : Bool) (values : Fin n → ℚ≥0) (i : ℕ) : Finset (Fin n) :=
  (candidates reversed values).getD i ∅

theorem at_eq {n : ℕ} (reversed : Bool) (values : Fin n → ℚ≥0) (i : ℕ) (hi : i<n) :
    candidate reversed values i=shore reversed values (values ⟨i,hi⟩) := by
  rw [candidate,List.getD_eq_get (candidates reversed values) ∅ (⟨i,by simpa only [length_candidates] using hi⟩ : Fin (candidates reversed values).length)]
  simp [candidates]

def valid {n : ℕ} (I : RationalInstance n) (reversed : Bool) (values : Fin n → ℚ≥0) (i : ℕ) : Prop :=
  CutSweeps.admissibleQ I (candidate reversed values i)
instance {n : ℕ} (I : RationalInstance n) (reversed : Bool) (values : Fin n → ℚ≥0) : DecidablePred (valid I reversed values) :=
  fun i => inferInstanceAs (Decidable (CutSweeps.admissibleQ I (candidate reversed values i)))
def score {n : ℕ} (I : RationalInstance n) (reversed : Bool) (values : Fin n → ℚ≥0) (i : ℕ) : ℚ≥0 :=
  CutScoreData.ratio I (candidate reversed values i)

end Lax455465Proofs.ThresholdCutData
