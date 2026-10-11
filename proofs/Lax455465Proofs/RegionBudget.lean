import Mathlib.Data.Nat.Log
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Lax455465Proofs.RegionBudget

/-- Number of rational grid cells needed by the deterministic search. Only
integer bit length is used by the algorithm. -/
def steps (p : ℕ) : ℕ := 2 * Nat.log2 p + 4

theorem steps_pos (p : ℕ) : 0 < steps p := by unfold steps; omega

/-- This many failed doublings exceed the two-volume budget 4p². -/
theorem exceeds_budget (p : ℕ) (hp : 0 < p) :
    4 * (p : ℚ) ^ 2 < (2 : ℚ) ^ steps p := by
  have hupperNat : p < 2 ^ (Nat.log2 p + 1) := by
    simpa only [Nat.log2_eq_log_two] using Nat.lt_pow_succ_log_self Nat.one_lt_two p
  have hupper : (p : ℚ) < (2 : ℚ) ^ (Nat.log2 p + 1) := by exact_mod_cast hupperNat
  have hpq : 0 < (p : ℚ) := by exact_mod_cast hp
  have hpow : 0 < (2 : ℚ) ^ (Nat.log2 p + 1) := pow_pos (by norm_num) _
  have hsquare : (p : ℚ) ^ 2 < ((2 : ℚ) ^ (Nat.log2 p + 1)) ^ 2 := by nlinarith
  have hid : (2 : ℚ) ^ steps p = 4 * ((2 : ℚ) ^ (Nat.log2 p + 1)) ^ 2 := by
    rw [show steps p = (Nat.log2 p + 1) * 2 + 2 by unfold steps; omega,
      pow_add, pow_mul]
    norm_num
    ring
  rw [hid]
  nlinarith

/-- The integer grid size contributes only a universal multiple of log₂ p
to the public approximation guarantee. -/
theorem steps_le_log (p : ℕ) (hp : 2 ≤ p) :
    (steps p : ℝ) ≤ 6 * (Real.log p / Real.log 2) := by
  have hpReal : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpNonzero : p ≠ 0 := by omega
  have hpowerNat : 2 ^ Nat.log2 p ≤ p := by
    simpa only [Nat.log2_eq_log_two] using Nat.pow_log_le_self 2 hpNonzero
  have hpower : (2 : ℝ) ^ Nat.log2 p ≤ p := by exact_mod_cast hpowerNat
  have hlog := Real.log_le_log (pow_pos (show (0 : ℝ) < 2 by norm_num) _) hpower
  rw [Real.log_pow] at hlog
  have hfloor : (Nat.log2 p : ℝ) ≤ Real.log p / Real.log 2 :=
    (le_div_iff₀ htwo).mpr hlog
  have hone : 1 ≤ Real.log p / Real.log 2 := by
    apply (le_div_iff₀ htwo).mpr
    simpa only [one_mul] using Real.log_le_log (show (0 : ℝ) < 2 by norm_num) hpReal
  unfold steps
  push_cast
  nlinarith

end Lax455465Proofs.RegionBudget
