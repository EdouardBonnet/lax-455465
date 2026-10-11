import Lax455465Proofs.RamSparseMemory

namespace Lax455465Proofs.RamWordOps

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

/-- Virtual arithmetic wraps at the chosen virtual modulus, independently
of the larger word size used to run the host program. -/
def reduce : Com := .assign "vm.result" (.sub (.var "vm.result")
  (.mul (.div (.var "vm.result") (.var "vm.modulus")) (.var "vm.modulus")))

theorem reduce_spec (B M value : ℕ) (hM : M < B) (hv : value < B) :
    Spec B (fun σ => σ.vars "vm.result" = value ∧ σ.vars "vm.modulus" = M) reduce
      (fun _ τ => τ.vars "vm.result" = value % M) 8 := by
  have hd : value / M < B := (Nat.div_le_self _ _).trans_lt hv
  have hp : value / M * M < B := (Nat.div_mul_le_self _ _).trans_lt hv
  have hr : value - value / M * M < B := (Nat.sub_le _ _).trans_lt hv
  rintro σ ⟨hsvalue, hsM⟩
  run_vcg
  all_goals simp_all [Nat.mod_def, Nat.mul_comm]

def binary (op : Bop) : Com :=
  .seq (.assign "vm.result" (.bin op (.var "vm.left") (.var "vm.right"))) reduce

theorem binary_spec (B M left right : ℕ) (op : Bop) (hM : M < B)
    (hl : left < B) (hr : right < B) (hop : op.apply left right < B) :
    Spec B (fun σ => σ.vars "vm.modulus" = M ∧ σ.vars "vm.left" = left ∧
      σ.vars "vm.right" = right) (binary op)
      (fun _ τ => τ.vars "vm.result" = op.apply left right % M) 12 := by
  rintro σ ⟨hsM, hsl, hsr⟩
  have hassign : Run B (.assign "vm.result" (.bin op (.var "vm.left") (.var "vm.right")))
      σ (σ.setVar "vm.result" (op.apply left right)) 4 :=
    Run.assign (evalB_bin (by simpa [hsl] using evalB_var (show σ.vars "vm.left" < B by omega))
      (by simpa [hsr] using evalB_var (show σ.vars "vm.right" < B by omega)) hop)
  obtain ⟨τ, hrun, hpost⟩ := reduce_spec B M (op.apply left right) hM hop
    (σ.setVar "vm.result" (op.apply left right)) (by simp [hsM])
  exact ⟨τ, hassign.seq hrun, hpost⟩

/-- Shifts by at least the virtual word length return zero. The host never
constructs the otherwise exponentially large intermediate. -/
def shift : Com := .ite (.lt (.var "vm.right") (.var "vm.width"))
  (binary .shiftl) (.assign "vm.result" (.lit 0))

theorem shift_spec (B w left right : ℕ) (hB : 2 * (2 ^ w) ^ 2 + 3 < B)
    (hl : left < 2 ^ w) (hr : right < 2 ^ w) :
    Spec B (fun σ => σ.vars "vm.modulus" = 2 ^ w ∧ σ.vars "vm.width" = w ∧
      σ.vars "vm.left" = left ∧ σ.vars "vm.right" = right) shift
      (fun _ τ => τ.vars "vm.result" = SparseRam.shiftValue w left right) 16 := by
  have hM : 2 ^ w < B := by nlinarith [Nat.two_pow_pos w]
  have hw : w < B := (Nat.lt_two_pow_self).trans hM
  have hlB := hl.trans hM
  have hrB := hr.trans hM
  have hzero : 0 < B := by omega
  have hsafe : right < w → Bop.shiftl.apply left right < B := by
    intro h
    have hp : 2 ^ right ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) h.le
    have hmul : left * 2 ^ right ≤ (2 ^ w) ^ 2 := by nlinarith
    exact hmul.trans_lt (by nlinarith)
  have hbranch : Spec B (fun σ => σ.vars "vm.modulus" = 2 ^ w ∧
      σ.vars "vm.left" = left ∧ σ.vars "vm.right" = right ∧ right < w)
      (binary .shiftl) (fun _ τ => τ.vars "vm.result" = left * 2 ^ right % 2 ^ w) 12 := by
    rintro σ ⟨hsM, hsl, hsr, h⟩
    exact binary_spec B (2 ^ w) left right .shiftl hM hlB hrB (hsafe h) σ ⟨hsM, hsl, hsr⟩
  rintro σ ⟨hsM, hsw, hsl, hsr⟩
  run_vcg [hbranch]
  all_goals simp_all [SparseRam.shiftValue]

/-- Bitwise complement is computed using the virtual mask. -/
def complement : Com := .assign "vm.result"
  (.sub (.sub (.var "vm.modulus") (.lit 1)) (.var "vm.left"))

theorem complement_spec (B w left : ℕ) (hB : 2 ^ w < B) (hl : left < 2 ^ w) :
    Spec B (fun σ => σ.vars "vm.modulus" = 2 ^ w ∧ σ.vars "vm.left" = left) complement
      (fun _ τ => τ.vars "vm.result" = 2 ^ w - 1 - left) 6 := by
  have h1 : 1 < B := by have := Nat.two_pow_pos w; omega
  have hlB := hl.trans hB
  have hmask : 2 ^ w - 1 < B := (Nat.sub_le _ _).trans_lt hB
  have hresult : 2 ^ w - 1 - left < B := (Nat.sub_le _ _).trans_lt hmask
  rintro σ ⟨hsM, hsl⟩
  run_vcg
  all_goals simp_all

theorem basic_bounds (w left right : ℕ) (hl : left < 2 ^ w) (hr : right < 2 ^ w) :
    left + right < 2 * (2 ^ w) ^ 2 + 3 ∧
    left - right < 2 * (2 ^ w) ^ 2 + 3 ∧
    left * right < 2 * (2 ^ w) ^ 2 + 3 ∧
    left / right < 2 * (2 ^ w) ^ 2 + 3 ∧
    Nat.land left right < 2 * (2 ^ w) ^ 2 + 3 := by
  have hM := Nat.two_pow_pos w
  have hlimit : 2 ^ w < 2 * (2 ^ w) ^ 2 + 3 := by nlinarith
  have hl' := hl.trans hlimit
  have hsub := (Nat.sub_le left right).trans_lt hl'
  have hdiv := (Nat.div_le_self left right).trans_lt hl'
  have hand : Nat.land left right ≤ left := Nat.and_le_left
  have hmul : left * right ≤ (2 ^ w) ^ 2 := by nlinarith
  exact ⟨by nlinarith, hsub, by nlinarith, hdiv, hand.trans_lt hl'⟩

def modulus : Com := .assign "vm.modulus" (.shiftl (.lit 1) (.var "vm.width"))

/-- The virtual modulus is computed once from the solver's polynomial
word-width bound; it does not query the host machine's word length. -/
theorem modulus_spec (B w : ℕ) (hB : 2 ^ w < B) :
    Spec B (fun σ => σ.vars "vm.width" = w) modulus
      (fun _ τ => τ.vars "vm.modulus" = 2 ^ w) 4 := by
  have h1 : 1 < B := by have := Nat.two_pow_pos w; omega
  have hw : w < B := Nat.lt_two_pow_self.trans hB
  rintro σ hσ
  run_vcg
  all_goals simp_all

end Lax455465Proofs.RamWordOps
