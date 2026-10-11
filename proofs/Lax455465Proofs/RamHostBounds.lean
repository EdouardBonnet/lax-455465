import Lax455465Proofs.RamVirtualConstants
import Lax455465Proofs.WordSize

namespace Lax455465Proofs.RamHostBounds

/-- This sufficient host width is polynomial whenever the virtual width,
source time and input length are polynomial. Program allowance is fixed. -/
def sufficient (w time allowance inputLength : ℕ) : ℕ :=
  2 * w + time + allowance + inputLength + 8

/-- The explicit virtual modulo arithmetic, all buffer counters, and the
fixed program literals fit at every sufficiently large host word width. -/
theorem sufficient_bounds (w time allowance inputLength W : ℕ)
    (hW : sufficient w time allowance inputLength ≤ W) :
    2 * (2 ^ w) ^ 2 + 3 < 2 ^ W ∧ time + 1 < 2 ^ W ∧
      allowance < 2 ^ W ∧ inputLength + 1 < 2 ^ W := by
  have hshift : 2 * w + 4 ≤ W := by unfold sufficient at hW; omega
  have hpow := Nat.pow_le_pow_right (show 1 ≤ 2 by decide) hshift
  have heq : 2 ^ (2 * w + 4) = 16 * (2 ^ w) ^ 2 := by
    rw [pow_add, show 2 * w = w + w by omega, pow_add]
    ring
  rw [heq] at hpow
  have hpos := Nat.two_pow_pos w
  refine ⟨by nlinarith, ?_, ?_, ?_⟩
  · have ht : time + 1 ≤ W := by unfold sufficient at hW; omega
    exact Nat.lt_two_pow_self.trans_le (Nat.pow_le_pow_right (by decide) ht)
  · have hc : allowance ≤ W := by unfold sufficient at hW; omega
    exact Nat.lt_two_pow_self.trans_le (Nat.pow_le_pow_right (by decide) hc)
  · have hl : inputLength + 1 ≤ W := by unfold sufficient at hW; omega
    exact Nat.lt_two_pow_self.trans_le (Nat.pow_le_pow_right (by decide) hl)

end Lax455465Proofs.RamHostBounds
