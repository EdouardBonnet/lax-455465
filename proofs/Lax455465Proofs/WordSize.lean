import Lax759944.BinaryWordEncoding
import Mathlib.Data.Nat.Size
import Mathlib.Tactic

namespace Lax455465Proofs.WordSize

open Lax759944.BinaryWordEncoding

theorem bitSize_nil : bitSize [] = 0 := rfl

theorem bitSize_cons (x : ℕ) (xs : List ℕ) : bitSize (x :: xs) = x.size + 1 + bitSize xs := by
  simp [bitSize, encode, encodeNat, Nat.size_eq_bits_len, Nat.add_comm, Nat.add_assoc]

theorem bitSize_append (xs ys : List ℕ) : bitSize (xs ++ ys) = bitSize xs + bitSize ys := by
  simp [bitSize, encode]

theorem length_le (xs : List ℕ) : xs.length ≤ bitSize xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => rw [bitSize_cons]; simp only [List.length_cons]; omega

theorem member_size (xs : List ℕ) (x : ℕ) (hx : x ∈ xs) : x.size + 1 ≤ bitSize xs := by
  induction xs with
  | nil => cases hx
  | cons y ys ih =>
    rw [bitSize_cons]
    rcases List.mem_cons.mp hx with he | ht
    · subst x; omega
    · have h := ih ht; omega

theorem member_bound (xs : List ℕ) (x : ℕ) (hx : x ∈ xs) : x < 2 ^ bitSize xs :=
  (Nat.lt_size_self x).trans_le (Nat.pow_le_pow_right (by decide) (by have := member_size xs x hx; omega))

theorem bounded_size (xs : List ℕ) (K : ℕ) (h : ∀ x ∈ xs, x.size ≤ K) :
    bitSize xs ≤ xs.length * (K + 1) := by
  induction xs with
  | nil => simp [bitSize_nil]
  | cons x xs ih =>
    have hx := h x List.mem_cons_self
    have ht := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
    rw [bitSize_cons]
    simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-- Halving a positive natural removes exactly one canonical binary digit. -/
theorem size_half (n : ℕ) (hn : 0 < n) : (n / 2).size + 1 = n.size := by
  induction n using Nat.binaryRec' with
  | zero => omega
  | bit b n h ih =>
    have hne : Nat.bit b n ≠ 0 := by omega
    rw [Nat.bit_div_two, Nat.size_bit hne]


end Lax455465Proofs.WordSize
