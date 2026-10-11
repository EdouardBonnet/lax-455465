import Lax455465Proofs.MaskedMassData
import Lax455465Proofs.RamBallMask
import Lax455465Proofs.RegionSelection

namespace Lax455465Proofs.BallMassData

open scoped BigOperators NNRat

def mask {n : ℕ} (distance : Fin n → ℚ≥0) (radius : ℚ≥0) : List ℚ≥0 :=
  (List.ofFn distance).map (fun q => RamBallMask.flag q radius)

def mass {n : ℕ} (weights distance : Fin n → ℚ≥0) (radius : ℚ≥0) : ℚ≥0 :=
  (RamMaskedSum.coefficients (List.ofFn weights) (mask distance radius)).sum

theorem mask_eq {n : ℕ} (distance : Fin n → ℚ≥0) (radius : ℚ≥0) :
    mask distance radius = MaskedMassData.flags (fun v => decide ((distance v : ℚ) < (radius : ℚ))) := by
  simp only [mask,List.map_ofFn,MaskedMassData.flags]
  congr 1
  funext v
  simp [RamBallMask.flag]

/-- The native mask-and-sum expression is the exact strict-ball mass used
by the region-selection theorem, including zero-weight transit vertices. -/
theorem coe_mass {n : ℕ} (weights distance : Fin n → ℚ≥0) (radius : ℚ≥0) :
    (mass weights distance radius : ℚ) =
      RegionSelection.ballMass (fun v => (weights v : ℚ)) (fun v => (distance v : ℚ)) radius := by
  unfold mass
  rw [mask_eq,MaskedMassData.coe_sum]
  simp only [RegionSelection.ballMass,RegionCharging.ball,Finset.sum_filter,decide_eq_true_eq]

end Lax455465Proofs.BallMassData
