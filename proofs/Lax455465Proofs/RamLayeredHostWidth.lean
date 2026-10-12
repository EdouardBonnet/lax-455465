import Lax455465Proofs.RamLayeredSolverBounds
import Lax455465Proofs.FlowEncodingSizes
import Lax455465Proofs.RamHostBounds

namespace Lax455465Proofs.RamLayeredHostWidth

open Lax759944.BinaryWordEncoding Lax455465.RationalEncoding LayeredFlowLP LayeredLpFlat RamLayeredData

/-- Fixed polynomial host width covers the graph arithmetic, LP input
construction, runtime width evaluation, and every virtual LP instruction. -/
noncomputable def wordBound (p : Lax808846.Ram.Program) (WB TB : Polynomial ℕ) : Polynomial ℕ :=
  let S := LayeredLpSize.sizeBound
  Polynomial.C 2*(Polynomial.X+WB.comp (S+Polynomial.C 1)) + TB.comp S +
    Polynomial.C (RamVirtualConstants.allowance p) + Polynomial.C 10*S + Polynomial.C 28

theorem wordBound_eval (p : Lax808846.Ram.Program) (WB TB : Polynomial ℕ) (L : ℕ) :
    (wordBound p WB TB).eval L =
      RamHostBounds.sufficient (L+WB.eval (LayeredLpSize.sizeBound.eval L+1))
        (TB.eval (LayeredLpSize.sizeBound.eval L)) (RamVirtualConstants.allowance p)
        (10*LayeredLpSize.sizeBound.eval L+20) := by
  simp [wordBound,Polynomial.eval_comp,RamHostBounds.sufficient]
  ring

/-- All construction and solver fit conditions hold at every larger
host word width; neither command queries or assumes the host width. -/
theorem sufficient (p : Lax808846.Ram.Program) (WB TB : Polynomial ℕ)
    {n : ℕ} (kind : Lax455465.ProductNetwork.EdgeKind) (I : RationalInstance n) (layers : ℕ) (hn : 2 ≤ n) (hlayers : layers ≤ n) (W : ℕ)
    (hW : (wordBound p WB TB).eval (bitSize (encodeInput kind I)) ≤ W) :
    let L := bitSize (encodeInput kind I)
    RamLayeredLpSolver.BuildFits (2^W) (2^L) n layers ∧
      RamFlowLpSolver.InvokeFits (2^W) p WB TB
        (bitSize (Lax109476.RationalEncoding.encodeProgram (program I layers))) := by
  let L := bitSize (encodeInput kind I)
  let s := bitSize (Lax109476.RationalEncoding.encodeProgram (program I layers))
  let S := LayeredLpSize.sizeBound.eval L
  let w := L+WB.eval (S+1)
  change RamLayeredLpSolver.BuildFits (2^W) (2^L) n layers ∧ RamFlowLpSolver.InvokeFits (2^W) p WB TB s
  have hs : s ≤ S := LayeredLpSize.polynomial_size kind I layers hlayers
  have hword : LayeredLpSize.wordLength n layers ≤ S := by
    rw [←LayeredLpSize.program_length I]
    exact (WordSize.length_le _).trans hs
  have hW' : RamHostBounds.sufficient w (TB.eval S) (RamVirtualConstants.allowance p) (10*S+20) ≤ W := by
    simpa only [wordBound_eval] using hW
  obtain ⟨hvirtual,hT,hallow,hsize⟩ := RamHostBounds.sufficient_bounds w (TB.eval S)
    (RamVirtualConstants.allowance p) (10*S+20) W hW'
  have hwW : w ≤ W := by dsimp only [RamHostBounds.sufficient] at hW'; omega
  have hwB : w < 2^W := Nat.lt_two_pow_self.trans_le (Nat.pow_le_pow_right (by decide) hwW)
  have hLP : WB.eval s ≤ w := by
    have := RamFlowSolverBounds.eval_mono WB (show s ≤ S+1 by omega); dsimp only [w]; omega
  have hLPnext : WB.eval (s+1) ≤ w := by
    have := RamFlowSolverBounds.eval_mono WB (show s+1 ≤ S+1 by omega); dsimp only [w]; omega
  have hpLP : 2^WB.eval s ≤ 2^w := Nat.pow_le_pow_right (by decide) hLP
  have hTmono := RamFlowSolverBounds.eval_mono TB hs
  have hL : L ≤ w := by dsimp only [w]; omega
  have hpL : 2^L ≤ 2^w := Nat.pow_le_pow_right (by decide) hL
  have hbuildWord : 2*(2^L)^2+3 < 2^W :=
    (Nat.add_le_add_right (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hpL 2)) 3).trans_lt hvirtual
  have hlpWord : 2*(2^WB.eval s)^2+3 < 2^W :=
    (Nat.add_le_add_right (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hpLP 2)) 3).trans_lt hvirtual
  have hrows : rows n layers ≤ S := by dsimp only [LayeredLpSize.wordLength] at hword; omega
  have hcols : columns n layers ≤ S := by dsimp only [LayeredLpSize.wordLength] at hword; omega
  have hmatrix : rows n layers*columns n layers ≤ S := by
    dsimp only [LayeredLpSize.wordLength] at hword; omega
  have hn2one : 1 ≤ n*n := by nlinarith
  have hn2 : n*n ≤ rows n layers := by dsimp only [rows]; omega
  have hbal : (n*n)*((layers+1)*n) ≤ rows n layers := by dsimp only [rows]; omega
  have hvertices : (layers+1)*n ≤ (n*n)*((layers+1)*n) := by
    simpa only [one_mul] using Nat.mul_le_mul_right ((layers+1)*n) hn2one
  have harcs : layers*(n*n) ≤ columns n layers := by
    have hh := Nat.mul_le_mul_right (layers*(n*n)) hn2one
    dsimp only [columns]
    nlinarith
  have hnSquare : n ≤ n*n := by nlinarith
  have hshape : shapeSize n layers ≤ 10*S+20 := by
    dsimp only [shapeSize]
    omega
  have hcap : 2*(n*n)+1 ≤ 10*S+20 := by omega
  refine ⟨?_,?_⟩
  · exact ⟨Nat.succ_le_iff.mpr (Nat.two_pow_pos L),(show 2^L ≤ 2*(2^L)^2+3 by nlinarith only [Nat.two_pow_pos L]).trans_lt hbuildWord,
      hshape.trans_lt (by omega),hcap.trans_lt (by omega),by omega⟩
  · exact ⟨by omega,hLPnext.trans_lt hwB,hlpWord,(Nat.add_le_add_right hTmono 1).trans_lt hT,hallow⟩

end Lax455465Proofs.RamLayeredHostWidth
