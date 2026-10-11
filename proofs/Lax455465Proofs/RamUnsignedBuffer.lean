import Lax455465Proofs.RamRational
import Lax455465Proofs.RamVirtualState
import Lax455465.RationalEncoding

namespace Lax455465Proofs.RamUnsignedBuffer

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamVirtualState
open Lax455465.RationalEncoding
open scoped NNRat

def encode (qs : List ℚ≥0) : List ℕ := qs.flatMap encodeRational

@[simp] theorem length_encode (qs : List ℚ≥0) : (encode qs).length = 2 * qs.length := by
  induction qs with
  | nil => rfl
  | cons q qs ih =>
    simp only [encode] at ih
    simp [encode,encodeRational,ih]; omega

theorem numerator_at (qs : List ℚ≥0) (i : ℕ) (hi : i < qs.length) :
    (encode qs)[2*i]? = some qs[i].num := by
  induction qs generalizing i with
  | nil => simp at hi
  | cons q qs ih =>
    cases i with
    | zero => simp [encode,encodeRational]
    | succ i =>
      have hi' : i < qs.length := by simpa using hi
      simpa only [encode,List.flatMap_cons,encodeRational,List.cons_append,List.nil_append,
        show 2*(i+1) = Nat.succ (Nat.succ (2*i)) by omega, List.getElem?_cons_succ,
        List.getElem_cons_succ] using ih i hi'

theorem denominator_at (qs : List ℚ≥0) (i : ℕ) (hi : i < qs.length) :
    (encode qs)[2*i+1]? = some qs[i].den := by
  induction qs generalizing i with
  | nil => simp at hi
  | cons q qs ih =>
    cases i with
    | zero => simp [encode,encodeRational]
    | succ i =>
      have hi' : i < qs.length := by simpa using hi
      simpa only [encode,List.flatMap_cons,encodeRational,List.cons_append,List.nil_append,
        show 2*(i+1)+1 = Nat.succ (Nat.succ (2*i+1)) by omega, List.getElem?_cons_succ,
        List.getElem_cons_succ] using ih i hi'

def read (array index : String) : Com :=
  .seq (.assign "rat.n" (.get array (.mul (.lit 2) (.var index))))
    (.seq (.assign "rat.d" (.get array (.add (.mul (.lit 2) (.var index)) (.lit 1))))
      (.assign "rat.s" (.lit 0)))

/-- Read an initialized canonical unsigned rational without a new gcd.
The index and copied buffer are preserved. -/
theorem read_spec (B : ℕ) (array index : String) (qs : List ℚ≥0) (i : ℕ)
    (hi : i < qs.length) (h2 : 2 < B) (hindex : 2*i+1 < B)
    (hn : qs[i].num < B) (hd : qs[i].den < B)
    (hfresh : index ≠ "rat.n" ∧ index ≠ "rat.d" ∧ index ≠ "rat.s") :
    Spec B (fun σ => Prefix (encode qs) array σ ∧ σ.vars index = i) (read array index)
      (fun _ τ => FractionOutput (qs[i] : ℚ) τ ∧ τ.vars "rat.s" = 0) 14 := by
  have hnum := numerator_at qs i hi
  have hden := denominator_at qs i hi
  rintro σ ⟨hp,hv⟩
  have hni : 2*i < (encode qs).length := by simp only [length_encode]; omega
  have hdi : 2*i+1 < (encode qs).length := by simp only [length_encode]; omega
  have hnumval : (encode qs)[2*i] = qs[i].num := by simpa only [List.getElem?_eq_getElem hni, Option.some.injEq] using hnum
  have hdenval : (encode qs)[2*i+1] = qs[i].den := by simpa only [List.getElem?_eq_getElem hdi, Option.some.injEq] using hden
  have hgN := (hp (2*i) hni).trans (congrArg some hnumval)
  have hgD := (hp (2*i+1) hdi).trans (congrArg some hdenval)
  have hN : 2*i < (σ.arrs array).length := by
    by_contra h; rw [List.getElem?_eq_none (by omega)] at hgN; cases hgN
  have hD : 2*i+1 < (σ.arrs array).length := by
    by_contra h; rw [List.getElem?_eq_none (by omega)] at hgD; cases hgD
  have hni' : i < B := by omega
  have hmul : 2*i < B := by omega
  have hvalue : fractionValue 0 qs[i].num qs[i].den = (qs[i] : ℚ) := by
    simp only [fractionValue, show ¬(0 : ℕ) = 1 by decide, if_false]
    exact congrArg (fun q : ℚ≥0 => (q : ℚ)) (NNRat.num_div_den qs[i])
  run_vcg
  all_goals simp_all [FractionOutput, NNRat.natAbs_num_coe, NNRat.den_coe]

end Lax455465Proofs.RamUnsignedBuffer
