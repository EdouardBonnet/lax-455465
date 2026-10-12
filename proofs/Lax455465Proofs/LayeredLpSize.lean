import Lax455465Proofs.LayeredLpFlat
import Lax455465Proofs.LpInputSize
import Lax455465Proofs.RamRational
import Lax455465Proofs.FlowEncodingSizes

namespace Lax455465Proofs.LayeredLpSize
open LayeredFlowLP LayeredLpFlat LpInputSize
open Lax455465.RationalEncoding Lax455465.ProductNetwork Lax759944.BinaryWordEncoding
open scoped NNRat

theorem height_half : Height 2 (1/2) := by
  simp [Height] <;> decide

theorem divergence_height {n L : ℕ} (b : Balance n L) : Height 2 (divergence b) := by
  simp only [divergence]
  split_ifs <;>
    first | simpa only [sub_self,sub_zero,zero_sub] using height_zero (by decide : 1 ≤ 2)
          | simpa only [sub_self,sub_zero,zero_sub] using height_half
          | simpa only [sub_self,sub_zero,zero_sub] using height_neg height_half

theorem balance_height {n L : ℕ} (b : Balance n L) (v : Variable n L) :
    Height 2 (balanceCoefficient b v) := by
  cases v with
  | inl _ => exact height_neg (divergence_height b)
  | inr a =>
    simp only [balanceCoefficient,incidence]
    split_ifs <;>
      first | simpa only [sub_self,sub_zero,zero_sub] using height_zero (by decide : 1 ≤ 2)
            | simpa only [sub_self,sub_zero,zero_sub] using height_one (by decide : 1 ≤ 2)
            | simpa only [sub_self,sub_zero,zero_sub] using height_neg (height_one (by decide : 1 ≤ 2))

theorem coefficient_height {n L : ℕ} (r : Row n L) (v : Variable n L) :
    Height 2 (LayeredFlowLP.coefficient r v) := by
  cases r with
  | inl e =>
    cases v with
    | inl _ => exact height_zero (by decide)
    | inr a =>
      simp only [LayeredFlowLP.coefficient,usage]
      split_ifs <;> norm_num [Height]
  | inr b =>
    simp only [LayeredFlowLP.coefficient]
    split_ifs
    · exact balance_height _ _
    · exact height_neg (balance_height _ _)

theorem program_heights {n : ℕ} (kind : EdgeKind) (I : RationalInstance n) (L : ℕ) :
    let M := 2^(bitSize (encodeInput kind I)+1)
    (∀ i j,Height M ((program I L).A i j)) ∧
    (∀ i,Height M ((program I L).b i)) ∧ (∀ j,Height M ((program I L).c j)) := by
  dsimp only
  have htwo : 2 ≤ 2^(bitSize (encodeInput kind I)+1) := by
    have hh := Nat.two_pow_pos (bitSize (encodeInput kind I))
    rw [pow_succ]
    omega
  refine ⟨fun i j => height_mono (coefficient_height _ _) htwo,?_,?_⟩
  · intro i
    simp only [program]
    cases (rowIndex n L).symm i with
    | inl e =>
      exact height_mono (capacity_height kind I e.1 e.2)
        (Nat.pow_le_pow_right (by decide) (by omega))
    | inr b => exact height_zero (by omega)
  · intro j
    simp only [program]
    cases (variableIndex n L).symm j with
    | inl _ => exact height_one (by omega)
    | inr _ => exact height_zero (by omega)

abbrev wordLength (n L : ℕ) := 2+3*(rows n L*columns n L+rows n L+columns n L)

theorem program_length {n : ℕ} (I : RationalInstance n) (L : ℕ) :
    (Lax109476.RationalEncoding.encodeProgram (program I L)).length=wordLength n L :=
  FlowEncodingSizes.program_length _

/-- Scanning at most n layer budgets keeps each dense LP polynomial in the
original binary graph encoding. No cut or path enumeration enters the LP. -/
theorem program_size {n : ℕ} (kind : EdgeKind) (I : RationalInstance n) (L : ℕ) (hL : L ≤ n) :
    bitSize (Lax109476.RationalEncoding.encodeProgram (program I L)) ≤
      256*(bitSize (encodeInput kind I)+1)^10 := by
  let S := bitSize (encodeInput kind I)
  let A := S+1
  let m := rows n L
  let v := columns n L
  have hn : n ≤ S := input_dimension kind I
  have hA : 1 ≤ A := by omega
  have hp := program_heights kind I L
  have hencoded := encoded_program_size (program I L) (S+1) hp.1 hp.2.1 hp.2.2
  have hm : m ≤ 3*A^4 := by
    have hLm : m ≤ n*n+2*((n*n)*((n+1)*n)) := by
      dsimp only [m,rows]
      gcongr
    have hh : n*n+2*((n*n)*((n+1)*n)) ≤ 3*(n+1)^4 := by nlinarith
    exact hLm.trans (hh.trans (Nat.mul_le_mul_left 3 (Nat.pow_le_pow_left (by omega : n+1 ≤ A) 4)))
  have hv : v ≤ 2*A^5 := by
    have hLv : v ≤ 1+(n*n)*(n*(n*n)) := by
      dsimp only [v,columns]
      gcongr
    have hh : 1+(n*n)*(n*(n*n)) ≤ 2*(n+1)^5 := by nlinarith
    exact hLv.trans (hh.trans (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left (by omega : n+1 ≤ A) 5)))
  have h4 : A^4 ≤ A^9 := Nat.pow_le_pow_right hA (by decide)
  have h5 : A^5 ≤ A^9 := Nat.pow_le_pow_right hA (by decide)
  have h9 : A^9 ≤ A^10 := Nat.pow_le_pow_right hA (by decide)
  have hpos : 1 ≤ A^9 := one_le_pow₀ hA
  have hmv : m*v ≤ 6*A^9 := by
    have hh := Nat.mul_le_mul hm hv
    convert hh using 1 <;> ring
  have hentries : m*v+m+v ≤ 11*A^9 := by nlinarith
  have hms : m.size ≤ m := Nat.size_le.mpr Nat.lt_two_pow_self
  have hvs : v.size ≤ v := Nat.size_le.mpr Nat.lt_two_pow_self
  have hheader : m.size+v.size+2 ≤ 7*A^9 := by nlinarith
  have hfactor : 2*(S+1)+6 ≤ 8*A := by omega
  have hproduct := Nat.mul_le_mul hentries hfactor
  have he : (11*A^9)*(8*A)=88*A^10 := by ring
  rw [he] at hproduct
  change bitSize (Lax109476.RationalEncoding.encodeProgram (program I L)) ≤
    m.size+v.size+2+(m*v+m+v)*(2*(S+1)+6) at hencoded
  change bitSize (Lax109476.RationalEncoding.encodeProgram (program I L)) ≤ 256*A^10
  exact hencoded.trans (by omega)

noncomputable def sizeBound : Polynomial ℕ := Polynomial.C 256*(Polynomial.X+Polynomial.C 1)^10

theorem polynomial_size {n : ℕ} (kind : EdgeKind) (I : RationalInstance n) (L : ℕ) (hL : L ≤ n) :
    bitSize (Lax109476.RationalEncoding.encodeProgram (program I L)) ≤
      sizeBound.eval (bitSize (encodeInput kind I)) := by
  simpa [sizeBound] using program_size kind I L hL

end Lax455465Proofs.LayeredLpSize
