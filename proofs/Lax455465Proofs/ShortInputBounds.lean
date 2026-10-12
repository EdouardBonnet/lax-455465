import Lax455465Proofs.RamIncidentMaximum
import Lax455465Proofs.RationalSumHeight
import Lax455465Proofs.RamShortTest

namespace Lax455465Proofs.ShortInputBounds
open Lax455465.RationalEncoding Lax455465.ProductNetwork Lax759944.BinaryWordEncoding
open scoped NNRat

/-- All incident-capacity prefixes have a quadratic bit-height bound in
the original input. Repeated additions use one common denominator lattice. -/
theorem row_prefix {n : ℕ} (kind : EdgeKind) (I : RationalInstance n) (v : Fin n) (k : ℕ) :
    let b := bitSize (encodeInput kind I)
    LpInputSize.Height (2^((b+1)^2)) (((RamIncidentSum.row I v).take k).sum : ℚ) := by
  let b := bitSize (encodeInput kind I)
  have hn : n≤b := LpInputSize.input_dimension kind I
  have hp := RationalSumHeight.prefix_dyadic_height (RamIncidentSum.row I v) b
    (by
      intro q hq
      obtain ⟨w,rfl⟩ := List.mem_ofFn.mp hq
      simpa only [NNRat.natAbs_num_coe] using (LpInputSize.capacity_height kind I v w).1)
    (by
      intro q hq
      obtain ⟨w,rfl⟩ := List.mem_ofFn.mp hq
      simpa only [NNRat.den_coe] using (LpInputSize.capacity_height kind I v w).2) k
  apply LpInputSize.height_mono hp
  apply Nat.pow_le_pow_right (by decide)
  simp only [RamIncidentSum.row,List.length_ofFn]
  nlinarith only [hn]

theorem maximum_height {n : ℕ} (kind : EdgeKind) (I : RationalInstance n) :
    let b := bitSize (encodeInput kind I)
    (ShortRationalParameters.maximum I).num ≤ 2^((b+1)^2) ∧
      (ShortRationalParameters.maximum I).den ≤ 2^((b+1)^2) := by
  rw [←RamIncidentMaximum.maximum_sums]
  apply RamUnsignedMaximum.maximum_height
  · exact Nat.succ_le_of_lt (Nat.two_pow_pos _)
  · intro q hq
    obtain ⟨v,rfl⟩ := List.mem_ofFn.mp hq
    have hp := (row_prefix kind I v n).1
    have he : (RamIncidentSum.row I v).length=n := by simp [RamIncidentSum.row]
    simpa only [List.take_of_length_le he.le,NNRat.natAbs_num_coe] using hp
  · intro q hq
    obtain ⟨v,rfl⟩ := List.mem_ofFn.mp hq
    have hp := (row_prefix kind I v n).2
    have he : (RamIncidentSum.row I v).length=n := by simp [RamIncidentSum.row]
    simpa only [List.take_of_length_le he.le,NNRat.den_coe] using hp

/-- Cross-products for the layer stopping test fit a polynomial host
width even when the exact LP output has large numerators and denominators. -/
theorem test_space (b n L w W : ℕ) (hn : n≤b) (hL : L≤b)
    (hW : 2*w+16*(b+1)^2+4 ≤ W) : RamShortTest.space n L (2^w)<2^W := by
  let M := 2^w
  let C := 16*(b+1)^2
  have hM : 1≤M := Nat.succ_le_of_lt (Nat.two_pow_pos w)
  have hsquare : 1≤(M+1)^2 := by nlinarith only [hM]
  have hnl : n*L≤b*b := Nat.mul_le_mul hn hL
  have hcoefficient : 4*n*L+1≤4*b*b+1 := by nlinarith only [hnl]
  have hsmall : n+L+4*n+10≤6*b+10 := by omega
  have hC : 4*b*b+1+(6*b+10)≤C := by dsimp [C]; nlinarith
  have hspace : RamShortTest.space n L M ≤ C*(M+1)^2 := by
    have h1 := Nat.mul_le_mul_right ((M+1)^2) hcoefficient
    have h2 := Nat.mul_le_mul_left (6*b+10) hsquare
    have h3 := Nat.mul_le_mul_right ((M+1)^2) hC
    dsimp only [RamShortTest.space]
    nlinarith only [h1,h2,h3,hsmall]
  have hM2 : (M+1)^2 ≤ 4*M^2 := by nlinarith only [hM]
  have hbound : C*(M+1)^2 ≤ 2^C*(4*M^2) :=
    Nat.mul_le_mul Nat.lt_two_pow_self.le hM2
  have he : 2^C*(4*M^2)=2^(C+2+2*w) := by
    dsimp only [M]
    rw [pow_add,pow_add,pow_mul]
    ring
  rw [he] at hbound
  have hfinal : 2^(C+2+2*w)<2^W := by
    apply Nat.pow_lt_pow_right (by decide)
    dsimp only [C]
    omega
  exact (hspace.trans hbound).trans_lt hfinal

end Lax455465Proofs.ShortInputBounds
