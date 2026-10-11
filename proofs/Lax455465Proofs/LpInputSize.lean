import Lax455465Proofs.DirectedFlowLP
import Lax455465Proofs.InstanceParser
import Lax455465Proofs.WordSize
import Mathlib.Data.Rat.Lemmas
import Lax109476.RationalEncoding

namespace Lax455465Proofs.LpInputSize

open Lax455465.RationalEncoding Lax455465.ProductNetwork
open Lax759944.BinaryWordEncoding DirectedFlowLP
open scoped NNRat

def Height (M : ℕ) (q : ℚ) : Prop := q.num.natAbs ≤ M ∧ q.den ≤ M

theorem height_zero {M : ℕ} (hM : 1 ≤ M) : Height M 0 := by simp [Height]; omega

theorem height_one {M : ℕ} (hM : 1 ≤ M) : Height M 1 := by simp [Height]; omega

theorem height_neg {M : ℕ} {q : ℚ} (h : Height M q) : Height M (-q) := by simpa [Height] using h

theorem height_mono {M N : ℕ} {q : ℚ} (h : Height M q) (hmn : M ≤ N) : Height N q :=
  ⟨h.1.trans hmn, h.2.trans hmn⟩

theorem height_mul {M N : ℕ} {q r : ℚ} (hq : Height M q) (hr : Height N r) :
    Height (M * N) (q * r) := by
  constructor
  · rw [Rat.mul_num]
    exact (Int.natAbs_ediv_le_natAbs _ _).trans
      (by simpa only [Int.natAbs_mul] using Nat.mul_le_mul hq.1 hr.1)
  · rw [Rat.mul_den]
    exact (Nat.div_le_self _ _).trans (Nat.mul_le_mul hq.2 hr.2)

theorem input_dimension {n : ℕ} (kind : EdgeKind) (I : RationalInstance n) :
    n ≤ bitSize (encodeInput kind I) := by
  apply le_trans (b := (encodeInput kind I).length) _ (WordSize.length_le _)
  simp only [encodeInput, List.length_append, InstanceParser.encoded_length, List.length_ofFn,
    List.length_cons, List.length_nil]
  omega

theorem weight_members {n : ℕ} (kind : EdgeKind) (I : RationalInstance n) (u : Fin n)
    (x : ℕ) (hx : x ∈ encodeRational (I.weight u)) : x ∈ encodeInput kind I := by
  simp only [encodeInput, List.mem_append]
  left; right
  apply List.mem_flatMap.mpr
  exact ⟨I.weight u, List.mem_ofFn.mpr ⟨u, rfl⟩, hx⟩

theorem capacity_members {n : ℕ} (kind : EdgeKind) (I : RationalInstance n) (u v : Fin n)
    (x : ℕ) (hx : x ∈ encodeRational (I.capacity u v)) : x ∈ encodeInput kind I := by
  simp only [encodeInput, List.mem_append]
  right
  apply List.mem_flatMap.mpr
  refine ⟨I.capacity u v, ?_, hx⟩
  apply List.mem_flatten.mpr
  exact ⟨List.ofFn (I.capacity u), List.mem_ofFn.mpr ⟨u, rfl⟩, List.mem_ofFn.mpr ⟨v, rfl⟩⟩

theorem weight_height {n : ℕ} (kind : EdgeKind) (I : RationalInstance n) (u : Fin n) :
    Height (2 ^ bitSize (encodeInput kind I)) (I.weight u : ℚ) := by
  have hn := WordSize.member_bound (encodeInput kind I) (I.weight u).num
    (weight_members kind I u _ (by simp [encodeRational]))
  have hd := WordSize.member_bound (encodeInput kind I) (I.weight u).den
    (weight_members kind I u _ (by simp [encodeRational]))
  exact ⟨by simpa only [NNRat.natAbs_num_coe] using hn.le, by simpa only [NNRat.den_coe] using hd.le⟩

theorem capacity_height {n : ℕ} (kind : EdgeKind) (I : RationalInstance n) (u v : Fin n) :
    Height (2 ^ bitSize (encodeInput kind I)) (I.capacity u v : ℚ) := by
  have hn := WordSize.member_bound (encodeInput kind I) (I.capacity u v).num
    (capacity_members kind I u v _ (by simp [encodeRational]))
  have hd := WordSize.member_bound (encodeInput kind I) (I.capacity u v).den
    (capacity_members kind I u v _ (by simp [encodeRational]))
  exact ⟨by simpa only [NNRat.natAbs_num_coe] using hn.le, by simpa only [NNRat.den_coe] using hd.le⟩

/-- Flow-LP coefficients use only zero, signed unit values, capacities,
and signed products of two vertex weights. Their heights grow quadratically. -/
theorem divergence_height {n : ℕ} (I : RationalInstance n) (M : ℕ) (hM : 1 ≤ M)
    (hw : ∀ u, Height M (I.weight u : ℚ)) (s t u : Fin n) :
    Height (M * M) (divergence I s t u) := by
  have hMM : 1 ≤ M * M := by nlinarith
  have hm := height_mul (hw s) (hw t)
  by_cases hst : s = t
  · simpa only [divergence, if_pos hst] using height_zero hMM
  by_cases hus : u = s
  · have hut : u ≠ t := by intro he; exact hst (hus.symm.trans he)
    simpa [divergence, hst, hus, hut, Ne.symm hst] using hm
  · by_cases hut : u = t
    · simpa [divergence, hst, hus, hut, Ne.symm hst] using height_neg hm
    · simpa [divergence, hst, hus, hut, Ne.symm hst] using height_zero hMM

theorem balance_height {n : ℕ} (I : RationalInstance n) (M : ℕ) (hM : 1 ≤ M)
    (hw : ∀ u, Height M (I.weight u : ℚ)) (b : Balance n) (v : Variable n) :
    Height (M * M) (balanceCoefficient I b v) := by
  have hMM : 1 ≤ M * M := by nlinarith
  cases v with
  | inl _ => exact height_neg (divergence_height I M hM hw _ _ _)
  | inr a =>
    simp only [balanceCoefficient]
    split_ifs <;>
      first | simpa only [sub_self, sub_zero, zero_sub] using height_zero hMM
            | simpa only [sub_self, sub_zero, zero_sub] using height_one hMM
            | simpa only [sub_self, sub_zero, zero_sub] using height_neg (height_one hMM)

theorem coefficient_height {n : ℕ} (I : RationalInstance n) (M : ℕ) (hM : 1 ≤ M)
    (hw : ∀ u, Height M (I.weight u : ℚ)) (r : Row n) (v : Variable n) :
    Height (M * M) (coefficient I r v) := by
  have hMM : 1 ≤ M * M := by nlinarith
  cases r with
  | inl e =>
    cases v with
    | inl _ => exact height_zero hMM
    | inr a =>
      simp only [coefficient]
      split_ifs <;> first | exact height_one hMM | exact height_zero hMM
  | inr sb =>
    simp only [coefficient]
    split_ifs
    · exact balance_height I M hM hw _ _
    · exact height_neg (balance_height I M hM hw _ _)

theorem program_heights {n : ℕ} (kind : EdgeKind) (I : RationalInstance n) :
    let M := 2 ^ bitSize (encodeInput kind I)
    (∀ i j, Height (M * M) ((program I).A i j)) ∧
    (∀ i, Height (M * M) ((program I).b i)) ∧
    (∀ j, Height (M * M) ((program I).c j)) := by
  dsimp only
  let M := 2 ^ bitSize (encodeInput kind I)
  have hM : 1 ≤ M := by have := Nat.two_pow_pos (bitSize (encodeInput kind I)); omega
  have hMM : 1 ≤ M * M := by nlinarith
  refine ⟨fun i j => coefficient_height I M hM (weight_height kind I) _ _, ?_, ?_⟩
  · intro i
    dsimp only [program, rowBound]
    cases (rowIndex n).symm i with
    | inl e => exact height_mono (capacity_height kind I e.1 e.2) (by nlinarith)
    | inr _ => exact height_zero hMM
  · intro j
    dsimp only [program, objective]
    cases (variableIndex n).symm j with
    | inl _ => exact height_one hMM
    | inr _ => exact height_zero hMM

theorem rational_size (q : ℚ) (K : ℕ) (h : Height (2 ^ K) q) :
    bitSize (Lax109476.RationalEncoding.encodeRational q) ≤ 2 * K + 6 := by
  have hp : 2 ^ K < 2 ^ (K + 1) := by rw [pow_succ]; have := Nat.two_pow_pos K; omega
  have hn := Nat.size_le.mpr (h.1.trans_lt hp)
  have hd := Nat.size_le.mpr (h.2.trans_lt hp)
  simp only [Lax109476.RationalEncoding.encodeRational, WordSize.bitSize_cons, WordSize.bitSize_nil]
  split_ifs <;> simp only [Nat.size_one, Nat.size_zero] <;> omega

private theorem rational_list_size (qs : List ℚ) (K : ℕ)
    (h : ∀ q ∈ qs, Height (2 ^ K) q) :
    bitSize (qs.flatMap Lax109476.RationalEncoding.encodeRational) ≤ qs.length * (2 * K + 6) := by
  induction qs with
  | nil => simp [WordSize.bitSize_nil]
  | cons q qs ih =>
    have hq := rational_size q K (h q List.mem_cons_self)
    have ht := ih (fun r hr => h r (List.mem_cons_of_mem q hr))
    simp only [List.flatMap_cons, WordSize.bitSize_append, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-- Dense rational LP encodings have size bounded by the number of entries
and their canonical numerator/denominator heights. -/
theorem encoded_program_size {m n : ℕ} (P : Lax109476.LinearProgram.Program ℚ m n) (K : ℕ)
    (hA : ∀ i j, Height (2 ^ K) (P.A i j)) (hb : ∀ i, Height (2 ^ K) (P.b i))
    (hc : ∀ j, Height (2 ^ K) (P.c j)) :
    bitSize (Lax109476.RationalEncoding.encodeProgram P) ≤
      m.size + n.size + 2 + (m * n + m + n) * (2 * K + 6) := by
  have hmat : ∀ q ∈ (List.ofFn fun i => List.ofFn (P.A i)).flatten, Height (2 ^ K) q := by
    intro q hq
    obtain ⟨row, hrow, hq⟩ := List.mem_flatten.mp hq
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hrow
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hq
    exact hA i j
  have hmatrix := rational_list_size _ K hmat
  have hrowlength : (List.ofFn fun i => List.ofFn (P.A i)).flatten.length = m * n := by
    simp [List.length_flatten, Function.comp_def, List.ofFn_const]
  rw [hrowlength] at hmatrix
  have hbsize := rational_list_size (List.ofFn P.b) K (by
    intro q hq; obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hq; exact hb i)
  have hcsize := rational_list_size (List.ofFn P.c) K (by
    intro q hq; obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hq; exact hc j)
  simp only [List.length_ofFn] at hbsize hcsize
  simp only [Lax109476.RationalEncoding.encodeProgram, Lax109476.RationalEncoding.encodeVector,
    WordSize.bitSize_append, WordSize.bitSize_cons, WordSize.bitSize_nil]
  nlinarith

/-- The flow-LP reduction expands the binary input by a fixed polynomial,
including the dimensions, all signed coefficients, and both RHS vectors. -/
theorem flow_program_size {n : ℕ} (kind : EdgeKind) (I : RationalInstance n) :
    bitSize (Lax109476.RationalEncoding.encodeProgram (program I)) ≤
      128 * (bitSize (encodeInput kind I) + 1) ^ 8 := by
  let L := bitSize (encodeInput kind I)
  let A := L + 1
  let m := n * n + 2 * ((n * n) * n)
  let v := 1 + (n * n) * (n * n)
  have hn : n ≤ L := input_dimension kind I
  have hA : 1 ≤ A := by omega
  have hheights := program_heights kind I
  have hp : 2 ^ L * 2 ^ L = 2 ^ (2 * L) := by rw [← pow_add]; congr 1; omega
  have hencoded := encoded_program_size (program I) (2 * L)
    (fun i j => by simpa only [← hp] using hheights.1 i j)
    (fun i => by simpa only [← hp] using hheights.2.1 i)
    (fun j => by simpa only [← hp] using hheights.2.2 j)
  have hm : m ≤ 3 * A ^ 3 := by
    have hs : m ≤ 3 * (n + 1) ^ 3 := by dsimp only [m]; nlinarith
    exact hs.trans (Nat.mul_le_mul_left 3 (Nat.pow_le_pow_left (by omega : n + 1 ≤ A) 3))
  have hv : v ≤ 2 * A ^ 4 := by
    have hs : v ≤ 2 * (n + 1) ^ 4 := by dsimp only [v]; nlinarith
    exact hs.trans (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left (by omega : n + 1 ≤ A) 4))
  have hpow3 : A ^ 3 ≤ A ^ 7 := Nat.pow_le_pow_right hA (by decide)
  have hpow4 : A ^ 4 ≤ A ^ 7 := Nat.pow_le_pow_right hA (by decide)
  have hpow7 : A ^ 7 ≤ A ^ 8 := Nat.pow_le_pow_right hA (by decide)
  have hpowpos : 1 ≤ A ^ 7 := by have := pow_pos (by omega : 0 < A) 7; omega
  have hmv : m * v ≤ 6 * A ^ 7 := by
    have h := Nat.mul_le_mul hm hv
    convert h using 1 <;> ring
  have hentries : m * v + m + v ≤ 11 * A ^ 7 := by nlinarith
  have hms : m.size ≤ m := Nat.size_le.mpr Nat.lt_two_pow_self
  have hvs : v.size ≤ v := Nat.size_le.mpr Nat.lt_two_pow_self
  have hheader : m.size + v.size + 2 ≤ 7 * A ^ 7 := by nlinarith
  have hq : 2 * (2 * L) + 6 ≤ 6 * A := by omega
  have hproduct := Nat.mul_le_mul hentries hq
  have hprodEq : (11 * A ^ 7) * (6 * A) = 66 * A ^ 8 := by ring
  rw [hprodEq] at hproduct
  change bitSize (Lax109476.RationalEncoding.encodeProgram (program I)) ≤
    m.size + v.size + 2 + (m * v + m + v) * (2 * (2 * L) + 6) at hencoded
  have htotal : m.size + v.size + 2 + (m * v + m + v) * (2 * (2 * L) + 6) ≤
      128 * A ^ 8 := by omega
  exact hencoded.trans htotal

noncomputable def sizeBound : Polynomial ℕ := Polynomial.C 128 * (Polynomial.X + Polynomial.C 1) ^ 8

theorem sizeBound_eval (L : ℕ) : sizeBound.eval L = 128 * (L + 1) ^ 8 := by simp [sizeBound]

theorem flow_program_polynomial_size {n : ℕ} (kind : EdgeKind) (I : RationalInstance n) :
    bitSize (Lax109476.RationalEncoding.encodeProgram (program I)) ≤
      sizeBound.eval (bitSize (encodeInput kind I)) := by
  rw [sizeBound_eval]
  exact flow_program_size kind I

end Lax455465Proofs.LpInputSize
