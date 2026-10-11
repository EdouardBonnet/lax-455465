import Lax455465Proofs.RationalParser

open scoped NNRat

namespace Lax455465Proofs.InstanceParser

open Lax455465.RationalEncoding Lax455465.ProductNetwork RationalParser

structure Decoded where
  order : ℕ
  kind : EdgeKind
  data : RationalInstance order

/-- Runtime coefficient lists are converted to a loopless instance.
Missing entries default to zero on malformed inputs. -/
def ofLists (n : ℕ) (weights : List ℚ≥0) (capacities : List (List ℚ≥0)) : RationalInstance n where
  capacity u v := if u = v then 0 else (capacities.getD u.val []).getD v.val 0
  loopless _ := by simp
  weight u := weights.getD u.val 0

/-- The dimension guard ensures malformed dimensions cannot start an
exponentially large dense-array computation. -/
def input : List ℕ → Option Decoded
  | tag :: n :: rest => if n ≤ rest.length then
      (vector n rest).bind fun wr =>
        (matrix n n wr.2).map fun cr =>
          ⟨n, if tag = 0 then .undirected else .directed, ofLists n wr.1 cr.1⟩
    else none
  | _ => none

theorem ofLists_encode {n : ℕ} (I : RationalInstance n) :
    ofLists n (List.ofFn I.weight) (List.ofFn fun u => List.ofFn (I.capacity u)) = I := by
  cases I with
  | mk capacity loopless weight =>
    dsimp only [ofLists]
    congr 1
    · funext u v
      by_cases huv : u = v
      · subst v
        simp [loopless]
      · simp [huv]
    · funext u
      simp

theorem encoded_length (qs : List ℚ≥0) : (qs.flatMap encodeRational).length = 2 * qs.length := by
  induction qs with
  | nil => rfl
  | cons q qs ih => simp [List.flatMap_cons, encodeRational, ih]; omega

/-- Canonical inputs recover their exact order, edge model, capacities,
and weights, including zero-dimensional instances. -/
theorem input_encode {n : ℕ} (kind : EdgeKind) (I : RationalInstance n) :
    input (encodeInput kind I) = some ⟨n, kind, I⟩ := by
  let weights := List.ofFn I.weight
  let rows := List.ofFn fun u => List.ofFn (I.capacity u)
  have hwlen : weights.length = n := by simp [weights]
  have hrlen : rows.length = n := by simp [rows]
  have hcols : ∀ row ∈ rows, row.length = n := by
    intro row hrow
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hrow
    simp
  have hv := vector_encode weights (rows.flatten.flatMap encodeRational)
  rw [hwlen] at hv
  have hm := matrix_encode n rows [] hcols
  simp only [List.append_nil, hrlen] at hm
  have hguard : n ≤ (weights.flatMap encodeRational ++ rows.flatten.flatMap encodeRational).length := by
    rw [List.length_append, encoded_length, hwlen]
    omega
  have hinstance := ofLists_encode I
  cases kind <;>
    simp only [encodeInput, List.cons_append, List.nil_append, input,
      show List.ofFn I.weight = weights from rfl,
      show (List.ofFn fun u => List.ofFn (I.capacity u)) = rows from rfl,
      if_pos hguard, hv, Option.bind_some, hm, Option.map_some] <;>
    simpa only [Nat.reduceEqDiff, if_true, if_false] using congrArg
      (fun J => some (Decoded.mk n _ J)) hinstance

end Lax455465Proofs.InstanceParser
