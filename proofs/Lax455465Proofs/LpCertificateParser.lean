import Lax109476.RationalEncoding
import Mathlib.Tactic

namespace Lax455465Proofs.LpCertificateParser

open Lax109476.RationalEncoding Lax109476.RationalCertificates

def value (sign num den : ℕ) : ℚ :=
  if sign = 1 then -(num : ℚ) / den else (num : ℚ) / den

/-- The LP output format uses a sign, magnitude, and denominator. -/
def rational : List ℕ → Option (ℚ × List ℕ)
  | sign :: num :: den :: rest => some (value sign num den, rest)
  | _ => none

def vector : ℕ → List ℕ → Option (List ℚ × List ℕ)
  | 0, input => some ([], input)
  | n + 1, input => (rational input).bind fun qr =>
      (vector n qr.2).map fun tail => (qr.1 :: tail.1, tail.2)

private theorem signed_num (z : ℤ) :
    (if z < 0 then -((z.natAbs : ℕ) : ℚ) else ((z.natAbs : ℕ) : ℚ)) = (z : ℚ) := by
  cases z <;> simp

theorem rational_encode (q : ℚ) (tail : List ℕ) :
    rational (encodeRational q ++ tail) = some (q, tail) := by
  unfold encodeRational
  simp only [List.cons_append, List.nil_append, rational, value]
  have hsign := signed_num q.num
  by_cases h : q.num < 0
  · simp only [if_pos h] at hsign ⊢
    rw [hsign, q.num_div_den]
    simp only [if_true]
  · simp only [if_neg h, show ¬(0 : ℕ) = 1 by decide, if_false] at hsign ⊢
    rw [hsign, q.num_div_den]

theorem vector_encode (qs : List ℚ) (tail : List ℕ) :
    vector qs.length (qs.flatMap encodeRational ++ tail) = some (qs, tail) := by
  induction qs with
  | nil => rfl
  | cons q qs ih =>
    simp only [List.length_cons, List.flatMap_cons, List.append_assoc, vector,
      rational_encode, Option.bind_some, ih, Option.map_some]

def vectorFunction (n : ℕ) (input : List ℕ) : Option ((Fin n → ℚ) × List ℕ) :=
  (vector n input).map fun result => (fun i => result.1.getD i.val 0, result.2)

theorem vectorFunction_encode {n : ℕ} (x : Fin n → ℚ) (tail : List ℕ) :
    vectorFunction n (encodeVector x ++ tail) = some (x, tail) := by
  have h := vector_encode (List.ofFn x) tail
  simp only [List.length_ofFn] at h
  simp only [vectorFunction, encodeVector, h, Option.map_some]
  congr 2
  funext i
  simp [List.getD_eq_getElem?_getD, i.isLt]

def certificate (m n : ℕ) : List ℕ → Option (Certificate m n × List ℕ)
  | 0 :: rest => (vectorFunction n rest).bind fun zr =>
      (vectorFunction m zr.2).map fun yr => (.optimal zr.1 yr.1, yr.2)
  | 1 :: rest => (vectorFunction m rest).map fun yr => (.infeasible yr.1, yr.2)
  | 2 :: rest => (vectorFunction n rest).bind fun zr =>
      (vectorFunction n zr.2).map fun dr => (.unbounded zr.1 dr.1, dr.2)
  | _ => none

/-- The parser reconstructs the same witnesses encoded by the registered
LP solver, for all outcomes and also in zero dimensions. -/
theorem certificate_encode {m n : ℕ} (c : Certificate m n) (tail : List ℕ) :
    certificate m n (encodeCertificate c ++ tail) = some (c, tail) := by
  cases c <;> simp only [encodeCertificate, List.cons_append, List.nil_append,
    List.append_assoc, certificate, vectorFunction_encode, Option.bind_some, Option.map_some]

end Lax455465Proofs.LpCertificateParser
