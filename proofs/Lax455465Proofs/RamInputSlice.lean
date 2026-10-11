import Lax455465Proofs.RamUnsignedBuffer

namespace Lax455465Proofs.RamInputSlice

open scoped NNRat

/-- Canonical pair indices inside a larger input word, retaining arbitrary
header words and an arbitrary unconsumed tail. -/
theorem numerator (front tail : List ℕ) (qs : List ℚ≥0) (i : ℕ) (hi : i < qs.length) :
    (front ++ (RamUnsignedBuffer.encode qs ++ tail))[front.length+2*i]? = some qs[i].num := by
  rw [List.getElem?_append_right (by omega),Nat.add_sub_cancel_left,
    List.getElem?_append_left (by rw [RamUnsignedBuffer.length_encode]; omega)]
  exact RamUnsignedBuffer.numerator_at qs i hi

theorem denominator (front tail : List ℕ) (qs : List ℚ≥0) (i : ℕ) (hi : i < qs.length) :
    (front ++ (RamUnsignedBuffer.encode qs ++ tail))[front.length+2*i+1]? = some qs[i].den := by
  rw [List.getElem?_append_right (by omega),show front.length+2*i+1-front.length = 2*i+1 by omega,
    List.getElem?_append_left (by rw [RamUnsignedBuffer.length_encode]; omega)]
  exact RamUnsignedBuffer.denominator_at qs i hi

theorem index_bound (front tail : List ℕ) (qs : List ℚ≥0) (i : ℕ) (hi : i < qs.length) :
    front.length+2*i+1 < (front ++ (RamUnsignedBuffer.encode qs ++ tail)).length := by
  simp only [List.length_append,RamUnsignedBuffer.length_encode]
  omega

end Lax455465Proofs.RamInputSlice
