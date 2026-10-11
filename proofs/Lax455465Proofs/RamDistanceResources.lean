import Lax455465Proofs.FlowDistanceBounds
import Lax455465Proofs.RamHostBounds

namespace Lax455465Proofs.RamDistanceResources

open Lax455465.RationalEncoding Lax455465.ProductNetwork
open Lax759944.BinaryWordEncoding

noncomputable def timeBound (sourceWord : Polynomial ℕ) : Polynomial ℕ :=
  (Polynomial.X+Polynomial.C 1)^3*(Polynomial.C 72*FlowDistanceBounds.widthBound sourceWord+Polynomial.C 400)

/-- The complete native Floyd–Warshall instruction count is polynomial
in the original graph encoding, including normalized rational arithmetic,
all matrix copies, and loop overhead. -/
theorem time_bound (sourceWord : Polynomial ℕ) {n : ℕ} (kind : EdgeKind) (I : RationalInstance n) :
    let L := bitSize (encodeInput kind I)
    let w := sourceWord.eval (bitSize (Lax109476.RationalEncoding.encodeProgram (DirectedFlowLP.program I)))
    n*((72*(w*(n*n+1))+324)*(n*n)+22)+10 ≤ (timeBound sourceWord).eval L := by
  dsimp only
  let L := bitSize (encodeInput kind I)
  let w := sourceWord.eval (bitSize (Lax109476.RationalEncoding.encodeProgram (DirectedFlowLP.program I)))
  let K := (FlowDistanceBounds.widthBound sourceWord).eval L
  have hn : n ≤ L := LpInputSize.input_dimension kind I
  have hs := LpInputSize.flow_program_polynomial_size kind I
  have hw : w ≤ sourceWord.eval (LpInputSize.sizeBound.eval L) := RamFlowSolverBounds.eval_mono sourceWord hs
  have hA : w*(n*n+1) ≤ K := by
    dsimp only [K,FlowDistanceBounds.widthBound]
    simp only [Polynomial.eval_mul,Polynomial.eval_comp,Polynomial.eval_add,Polynomial.eval_pow,
      Polynomial.eval_X,Polynomial.eval_C]
    exact Nat.mul_le_mul hw (by nlinarith)
  have hcubed : n*n*n ≤ (L+1)^3 := by
    calc
      _ ≤ (L+1)*(L+1)*(L+1) := Nat.mul_le_mul (Nat.mul_le_mul (by omega : n ≤ L+1) (by omega : n ≤ L+1)) (by omega)
      _ = _ := by ring
  have hmain := Nat.mul_le_mul hcubed (Nat.add_le_add_right (Nat.mul_le_mul_left 72 hA) 324)
  have hnCube : n ≤ (L+1)^3 := (by omega : n ≤ L+1).trans (Nat.le_self_pow (by decide) (L+1))
  have hCubePos : 1 ≤ (L+1)^3 := Nat.succ_le_iff.mpr (pow_pos (by omega) 3)
  have hrem : 22*n+10 ≤ 76*(L+1)^3 := by omega
  change n*((72*(w*(n*n+1))+324)*(n*n)+22)+10 ≤ _
  simp only [timeBound,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_C]
  change n*((72*(w*(n*n+1))+324)*(n*n)+22)+10 ≤ (L+1)^3*(72*K+400)
  nlinarith

theorem width_bound (sourceWord : Polynomial ℕ) {n : ℕ} (kind : EdgeKind) (I : RationalInstance n) :
    sourceWord.eval (bitSize (Lax109476.RationalEncoding.encodeProgram (DirectedFlowLP.program I)))*(n*n+1) ≤
      (FlowDistanceBounds.widthBound sourceWord).eval (bitSize (encodeInput kind I)) := by
  let L := bitSize (encodeInput kind I)
  have hn : n ≤ L := LpInputSize.input_dimension kind I
  have hs := LpInputSize.flow_program_polynomial_size kind I
  have hw := RamFlowSolverBounds.eval_mono sourceWord hs
  simp only [FlowDistanceBounds.widthBound,Polynomial.eval_mul,Polynomial.eval_comp,
    Polynomial.eval_add,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_C]
  exact Nat.mul_le_mul hw (by change n*n+1 ≤ L^2+1; nlinarith)

/-- A polynomial host width covers every intermediate distance operation
at all larger word widths, including raw gcd and comparison products. -/
theorem host_bound (sourceWord : Polynomial ℕ) {n : ℕ} (kind : EdgeKind) (I : RationalInstance n) (W : ℕ)
    (hW : 2*(FlowDistanceBounds.widthBound sourceWord).eval (bitSize (encodeInput kind I))+
      LpInputSize.sizeBound.eval (bitSize (encodeInput kind I))+20 ≤ W) :
    let w := sourceWord.eval (bitSize (Lax109476.RationalEncoding.encodeProgram (DirectedFlowLP.program I)))
    2*(2*2^(w*(n*n+1)))^2+3 < 2^W ∧ n < 2^W ∧ n*n < 2^W ∧ 2*(n*n)+2 < 2^W := by
  let L := bitSize (encodeInput kind I)
  let K := (FlowDistanceBounds.widthBound sourceWord).eval L
  let S := LpInputSize.sizeBound.eval L
  let A := sourceWord.eval (bitSize (Lax109476.RationalEncoding.encodeProgram (DirectedFlowLP.program I)))*(n*n+1)
  have hA : A ≤ K := width_bound sourceWord kind I
  have hsuff : RamHostBounds.sufficient (K+2) 0 0 (S+3) ≤ W := by
    dsimp only [RamHostBounds.sufficient]
    change 2*(K+2)+0+0+(S+3)+8 ≤ W
    change 2*K+S+20 ≤ W at hW
    omega
  obtain ⟨hv,_,_,hlen⟩ := RamHostBounds.sufficient_bounds (K+2) 0 0 (S+3) W hsuff
  have hpow : 2*2^A ≤ 2^(K+2) := by
    calc
      _ = 2^(A+1) := by rw [Nat.pow_succ]; ring
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)
  have hword : RamFlowLp.wordLength n ≤ S := by
    rw [←FlowEncodingSizes.flow_length I]
    exact (WordSize.length_le _).trans (LpInputSize.flow_program_polynomial_size kind I)
  have hn2 : n*n ≤ S := by dsimp only [RamFlowLp.wordLength,RamFlowData.rows] at hword; omega
  have hn : n ≤ n*n+1 := by nlinarith
  have hindex : 2*(n*n)+2 ≤ S+3 := by dsimp only [RamFlowLp.wordLength,RamFlowData.rows] at hword; omega
  refine ⟨(Nat.add_le_add_right (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hpow 2)) 3).trans_lt hv,?_,?_,?_⟩
  · omega
  · omega
  · omega

end Lax455465Proofs.RamDistanceResources

