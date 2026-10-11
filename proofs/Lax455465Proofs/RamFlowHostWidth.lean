import Lax455465Proofs.RamFlowSolverBounds
import Lax455465Proofs.FlowEncodingSizes
import Lax455465Proofs.RamHostBounds

namespace Lax455465Proofs.RamFlowHostWidth

open Lax759944.BinaryWordEncoding Lax455465.RationalEncoding DirectedFlowLP RamFlowData

/-- Fixed polynomial host width covers the graph arithmetic, LP input
construction, runtime width evaluation, and every virtual LP instruction. -/
noncomputable def wordBound (p : Lax808846.Ram.Program) (WB TB : Polynomial ℕ) : Polynomial ℕ :=
  let S := LpInputSize.sizeBound
  Polynomial.C 2*(Polynomial.X+WB.comp (S+Polynomial.C 1)) + TB.comp S +
    Polynomial.C (RamVirtualConstants.allowance p) + S + Polynomial.C 11

theorem wordBound_eval (p : Lax808846.Ram.Program) (WB TB : Polynomial ℕ) (L : ℕ) :
    (wordBound p WB TB).eval L =
      RamHostBounds.sufficient (L+WB.eval (LpInputSize.sizeBound.eval L+1))
        (TB.eval (LpInputSize.sizeBound.eval L)) (RamVirtualConstants.allowance p)
        (LpInputSize.sizeBound.eval L+3) := by
  simp [wordBound,Polynomial.eval_comp,RamHostBounds.sufficient]
  ring

/-- All construction and solver fit conditions hold at every larger
host word width; neither command queries or assumes the host width. -/
theorem sufficient (p : Lax808846.Ram.Program) (WB TB : Polynomial ℕ)
    {n : ℕ} (kind : Lax455465.ProductNetwork.EdgeKind) (I : RationalInstance n) (W : ℕ)
    (hW : (wordBound p WB TB).eval (bitSize (encodeInput kind I)) ≤ W) :
    let L := bitSize (encodeInput kind I)
    RamFlowLpSolver.BuildFits (2^W) (2^L) n ∧
      RamFlowLpSolver.InvokeFits (2^W) p WB TB
        (bitSize (Lax109476.RationalEncoding.encodeProgram (program I))) := by
  let L := bitSize (encodeInput kind I)
  let s := bitSize (Lax109476.RationalEncoding.encodeProgram (program I))
  let S := LpInputSize.sizeBound.eval L
  let w := L+WB.eval (S+1)
  change RamFlowLpSolver.BuildFits (2^W) (2^L) n ∧ RamFlowLpSolver.InvokeFits (2^W) p WB TB s
  have hs : s ≤ S := LpInputSize.flow_program_polynomial_size kind I
  have hword : RamFlowLp.wordLength n ≤ S := by
    rw [←FlowEncodingSizes.flow_length I]
    exact (WordSize.length_le _).trans hs
  have hW' : RamHostBounds.sufficient w (TB.eval S) (RamVirtualConstants.allowance p) (S+3) ≤ W := by
    simpa only [wordBound_eval] using hW
  obtain ⟨hvirtual,hT,hallow,hsize⟩ := RamHostBounds.sufficient_bounds w (TB.eval S)
    (RamVirtualConstants.allowance p) (S+3) W hW'
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
  have hrows : rows n ≤ S := by dsimp only [RamFlowLp.wordLength] at hword; omega
  have hcols : columns n ≤ S := by dsimp only [RamFlowLp.wordLength] at hword; omega
  have hmatrix : rows n*columns n ≤ S := by dsimp only [RamFlowLp.wordLength] at hword; omega
  have hn2 : n*n ≤ rows n := by dsimp only [rows]; omega
  have hn3 : (n*n)*n ≤ rows n := by dsimp only [rows]; omega
  have hcap : 2*(n*n)+1 ≤ S+3 := by dsimp only [RamFlowLp.wordLength] at hword; omega
  have hni : 2*n+1 ≤ S+3 := by
    have hnn : n ≤ n*n+1 := by nlinarith
    dsimp only [RamFlowLp.wordLength] at hword; omega
  refine ⟨?_,?_⟩
  · exact ⟨Nat.succ_le_iff.mpr (Nat.two_pow_pos L),hbuildWord,hni.trans_lt (by omega),
      (hn2.trans hrows).trans_lt (by omega),(hn3.trans hrows).trans_lt (by omega),
      hrows.trans_lt (by omega),hcols.trans_lt (by omega),hmatrix.trans_lt (by omega),
      hcap.trans_lt (by omega),by omega⟩
  · exact ⟨by omega,hLPnext.trans_lt hwB,hlpWord,(Nat.add_le_add_right hTmono 1).trans_lt hT,hallow⟩

end Lax455465Proofs.RamFlowHostWidth
