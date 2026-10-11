import Lax455465Proofs.VolumeHeight
import Lax455465Proofs.RamHostBounds
import Lax455465Proofs.LpInputSize

namespace Lax455465Proofs.RamVolumeResources

open Lax455465.RationalEncoding Lax455465.ProductNetwork Lax759944.BinaryWordEncoding

noncomputable def heightBound (coordinateWord : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C 3*(Polynomial.C 4*coordinateWord*(Polynomial.X^2+Polynomial.C 1)+Polynomial.X^2+Polynomial.C 1)+Polynomial.C 1

noncomputable def timeBound (coordinateWord : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C 1000*(heightBound coordinateWord+Polynomial.C 1)*(Polynomial.X^2+Polynomial.C 1)+Polynomial.C 192

noncomputable def wordBound (coordinateWord : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C 2*heightBound coordinateWord+Polynomial.C 2*Polynomial.X^2+Polynomial.C 2*Polynomial.X+Polynomial.C 20

theorem height_bound (coordinateWord : Polynomial ℕ) {n : ℕ} (kind : EdgeKind) (I : RationalInstance n) :
    VolumeHeight.exponent n (coordinateWord.eval (bitSize (encodeInput kind I))) ≤
      (heightBound coordinateWord).eval (bitSize (encodeInput kind I)) := by
  let L := bitSize (encodeInput kind I)
  have hn : n ≤ L := LpInputSize.input_dimension kind I
  have hnn : n*n+1 ≤ L^2+1 := by nlinarith
  have hmul := Nat.mul_le_mul_left (4*coordinateWord.eval L) hnn
  simp only [heightBound,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,Polynomial.eval_pow]
  dsimp only [VolumeHeight.exponent,VolumeHeight.sumExponent,L] at hmul ⊢
  nlinarith

theorem time_bound (coordinateWord : Polynomial ℕ) {n : ℕ} (kind : EdgeKind) (I : RationalInstance n) :
    (216*VolumeHeight.exponent n (coordinateWord.eval (bitSize (encodeInput kind I)))+610)*(n*n)+
      72*VolumeHeight.exponent n (coordinateWord.eval (bitSize (encodeInput kind I)))+192 ≤
      (timeBound coordinateWord).eval (bitSize (encodeInput kind I)) := by
  let L := bitSize (encodeInput kind I)
  let H := (heightBound coordinateWord).eval L
  let V := VolumeHeight.exponent n (coordinateWord.eval L)
  have hn : n ≤ L := LpInputSize.input_dimension kind I
  have hv : V ≤ H := height_bound coordinateWord kind I
  have hnn : n*n ≤ L^2 := by nlinarith
  have hfirst : (216*V+610)*(n*n) ≤ (216*H+610)*L^2 := Nat.mul_le_mul (by omega) hnn
  have hrest : 72*V ≤ 72*H := by omega
  have hh : (216*V+610)*(n*n)+72*V+192 ≤ 1000*(H+1)*(L^2+1)+192 := by nlinarith
  simpa only [L,H,V,timeBound,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,Polynomial.eval_pow] using hh

theorem host_bound (coordinateWord : Polynomial ℕ) {n : ℕ} (kind : EdgeKind) (I : RationalInstance n) (W : ℕ)
    (hW : (wordBound coordinateWord).eval (bitSize (encodeInput kind I)) ≤ W) :
    2*(2^(VolumeHeight.exponent n (coordinateWord.eval (bitSize (encodeInput kind I)))))^2+3 < 2^W ∧
      2*(n*n)+2 < 2^W ∧ 2*n+2 < 2^W := by
  let L := bitSize (encodeInput kind I)
  let V := VolumeHeight.exponent n (coordinateWord.eval L)
  have hn : n ≤ L := LpInputSize.input_dimension kind I
  have hv := height_bound coordinateWord kind I
  have hwidth : RamHostBounds.sufficient V 0 0 (2*(n*n)+2*n+3) ≤ W := by
    simp only [wordBound,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,Polynomial.eval_pow] at hW
    dsimp only [RamHostBounds.sufficient,V,L]
    have hnn : n*n ≤ L^2 := by nlinarith
    dsimp only [L] at hnn hn hv
    omega
  obtain ⟨hB,hT,hC,hL⟩ := RamHostBounds.sufficient_bounds V 0 0 (2*(n*n)+2*n+3) W hwidth
  exact ⟨hB,by omega,by omega⟩

end Lax455465Proofs.RamVolumeResources
