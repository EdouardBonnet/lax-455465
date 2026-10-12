import Lax455465Proofs.RegionRounding
import Lax455465Proofs.MetricCostData
import Lax455465Proofs.UnsignedHeight

namespace Lax455465Proofs.RoundingConstants
open scoped NNRat

def seed (cost : ℚ≥0) (p : ℕ) : ℚ≥0 := cost/(p : ℚ≥0)
def delta (total : ℚ≥0) : ℚ≥0 := (4*total^2)⁻¹
def beta (total : ℚ≥0) (p : ℕ) : ℚ≥0 := (RegionBudget.steps p : ℚ≥0)/(delta total)
def gridStep (total : ℚ≥0) (p : ℕ) : ℚ≥0 := delta total/(RegionBudget.steps p : ℚ≥0)

theorem coe_delta (total : ℚ≥0) : (delta total : ℚ) = 1/(4*(total : ℚ)^2) := by
  simp [delta]

theorem coe_beta (total : ℚ≥0) (p : ℕ) :
    (beta total p : ℚ) = RegionSearch.slope (RegionBudget.steps p) (delta total) := by
  simp [beta,RegionSearch.slope]

theorem inverse_height {M : ℕ} {q : ℚ≥0} (hM : 1≤M) (hq : LpInputSize.Height M (q : ℚ)) :
    LpInputSize.Height M ((q⁻¹ : ℚ≥0) : ℚ) := by
  simp only [LpInputSize.Height,NNRat.coe_inv,Rat.num_inv,Rat.den_inv]
  have habs : (q : ℚ).num.sign.natAbs≤1 := by
    rw [Int.natAbs_sign]; split_ifs <;> omega
  constructor
  · simpa only [Int.natAbs_mul,Int.natAbs_natCast,Nat.one_mul] using
      (Nat.mul_le_mul habs hq.2)
  · split_ifs
    · exact hM
    · exact hq.1

end Lax455465Proofs.RoundingConstants
