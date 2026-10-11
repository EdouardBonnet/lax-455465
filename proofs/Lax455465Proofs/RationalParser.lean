import Lax455465.RationalEncoding
import Mathlib.Tactic

open scoped NNRat

namespace Lax455465Proofs.RationalParser

open Lax455465.RationalEncoding

def rational : List ℕ → Option (ℚ≥0 × List ℕ)
  | num :: den :: rest => some (NNRat.divNat num den, rest)
  | _ => none

def vector : ℕ → List ℕ → Option (List ℚ≥0 × List ℕ)
  | 0, input => some ([], input)
  | n + 1, input => (rational input).bind fun qr =>
      (vector n qr.2).map fun tail => (qr.1 :: tail.1, tail.2)

def matrix (cols : ℕ) : ℕ → List ℕ → Option (List (List ℚ≥0) × List ℕ)
  | 0, input => some ([], input)
  | rows + 1, input => (vector cols input).bind fun rr =>
      (matrix cols rows rr.2).map fun tail => (rr.1 :: tail.1, tail.2)

/-- Every canonical nonnegative rational is recovered with its exact tail. -/
theorem rational_encode (q : ℚ≥0) (tail : List ℕ) :
    rational (encodeRational q ++ tail) = some (q, tail) := by
  simp only [encodeRational, List.cons_append, List.nil_append, rational, NNRat.num_divNat_den]

/-- The parser consumes precisely the encoded vector, leaving all
following words available to the next stage. -/
theorem vector_encode (qs : List ℚ≥0) (tail : List ℕ) :
    vector qs.length (qs.flatMap encodeRational ++ tail) = some (qs, tail) := by
  induction qs with
  | nil => rfl
  | cons q qs ih =>
    simp only [List.length_cons, List.flatMap_cons, List.append_assoc, vector,
      rational_encode, Option.bind_some, ih, Option.map_some]

/-- Matrix rows are read in the same row order used by the public input
encoding. The row and column counts are runtime data. -/
theorem matrix_encode (cols : ℕ) (rows : List (List ℚ≥0)) (tail : List ℕ)
    (hcols : ∀ row ∈ rows, row.length = cols) :
    matrix cols rows.length (rows.flatten.flatMap encodeRational ++ tail) = some (rows, tail) := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    have hr : row.length = cols := hcols row (List.mem_cons_self)
    have ht : ∀ r ∈ rows, r.length = cols := fun r hm => hcols r (List.mem_cons_of_mem _ hm)
    simp only [List.length_cons, List.flatten_cons, List.flatMap_append, List.append_assoc, matrix]
    have hv := vector_encode row (rows.flatten.flatMap encodeRational ++ tail)
    rw [hr] at hv
    rw [hv, Option.bind_some, ih ht, Option.map_some]

end Lax455465Proofs.RationalParser
