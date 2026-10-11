import Lax455465Proofs.RamFlowLp

namespace Lax455465Proofs.RamFlowLpBounds

open RamFlowData

/-- Dense construction, including rational reduction and all output words,
has polynomial instruction cost in the original binary input size. -/
theorem cost_bound (n L : ℕ) (hn : n ≤ L) :
    RamFlowLp.cost n (2^L) ≤ 10000*(L+1)^8 := by
  let a := L+1
  have ha : 1 ≤ a := by omega
  have hnA : n ≤ a := by omega
  have hsz : ((2^L)*(2^L)).size = 2*L+1 := by
    rw [←pow_add,Nat.size_pow]
    omega
  have hn2 : n*n ≤ a^2 := by nlinarith
  have hn3 : (n*n)*n ≤ a^3 := by
    calc _ ≤ a^2*a := Nat.mul_le_mul hn2 hnA
         _ = a^3 := by ring
  have hn4 : (n*n)*(n*n) ≤ a^4 := by
    calc _ ≤ a^2*a^2 := Nat.mul_le_mul hn2 hn2
         _ = a^4 := by ring
  have ha23 : a^2 ≤ a^3 := by exact Nat.pow_le_pow_right ha (by decide)
  have hrows : rows n ≤ 3*a^3 := by dsimp only [rows]; omega
  have hcols : columns n ≤ 2*a^4 := by
    have ha4 : 1 ≤ a^4 := by have := pow_pos (by omega : 0<a) 4; omega
    dsimp only [columns]; omega
  have hmatrix : rows n*columns n ≤ 6*a^7 := by
    calc _ ≤ (3*a^3)*(2*a^4) := Nat.mul_le_mul hrows hcols
         _ = 6*a^7 := by ring
  have hfactor : 36*((2^L)*(2^L)).size+239 ≤ 400*a := by rw [hsz]; omega
  have hmain : (36*((2^L)*(2^L)).size+239)*(rows n*columns n) ≤ 2400*a^8 := by
    calc _ ≤ (400*a)*(6*a^7) := Nat.mul_le_mul hfactor hmatrix
         _ = 2400*a^8 := by ring
  have ha38 : a^3 ≤ a^8 := Nat.pow_le_pow_right ha (by decide)
  have ha48 : a^4 ≤ a^8 := Nat.pow_le_pow_right ha (by decide)
  have ha8 : 1 ≤ a^8 := by have := pow_pos (by omega : 0<a) 8; omega
  have hrow8 : rows n ≤ 3*a^8 := by omega
  have hcol8 : columns n ≤ 2*a^8 := by omega
  change (36*((2^L)*(2^L)).size+239)*(rows n*columns n)+53*rows n+45*columns n+34 ≤ 10000*a^8
  omega

end Lax455465Proofs.RamFlowLpBounds
