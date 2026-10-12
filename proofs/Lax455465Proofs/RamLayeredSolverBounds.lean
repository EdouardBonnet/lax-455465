import Lax455465Proofs.RamFlowSolverBounds
import Lax455465Proofs.RamLayeredLpSolver
import Lax455465Proofs.LpInputSize

namespace Lax455465Proofs.RamLayeredSolverBounds

open Lax759944.BinaryWordEncoding Lax455465.RationalEncoding LayeredFlowLP LayeredLpFlat

open RamFlowSolverBounds

noncomputable def timeBound (p : Lax808846.Ram.Program) (coefficients : List ℕ) (TB : Polynomial ℕ) : Polynomial ℕ :=
  let S := LayeredLpSize.sizeBound
  let T := TB.comp S
  Polynomial.C 300*S+Polynomial.C 34 +
    (Polynomial.C 12*S+Polynomial.C 39)*S+Polynomial.C (6*coefficients.length+29)+
    (T+Polynomial.C 1)*(Polynomial.C (4*p.length+104)+Polynomial.C 32*T)+Polynomial.C 18

theorem timeBound_eval (p : Lax808846.Ram.Program) (coefficients : List ℕ) (TB : Polynomial ℕ) (L : ℕ) :
    (timeBound p coefficients TB).eval L = 300*LayeredLpSize.sizeBound.eval L+34+
      (12*LayeredLpSize.sizeBound.eval L+39)*LayeredLpSize.sizeBound.eval L+6*coefficients.length+29+
      (TB.eval (LayeredLpSize.sizeBound.eval L)+1)*(4*p.length+32*TB.eval (LayeredLpSize.sizeBound.eval L)+104)+18 := by
  simp [timeBound,Polynomial.eval_comp]
  ring

/-- Construction, runtime size measurement, framing and the complete
registered LP execution have one polynomial instruction bound in the
original flow input size. The source program and both polynomials are fixed. -/
theorem cost_bound (p : Lax808846.Ram.Program) (coefficients : List ℕ) (TB : Polynomial ℕ)
    {n : ℕ} (kind : Lax455465.ProductNetwork.EdgeKind) (I : RationalInstance n) (layers : ℕ) (hlayers : layers ≤ n) :
    let L := bitSize (encodeInput kind I)
    RamLayeredLp.cost n layers+RamFlowLpSolver.invocationCost p coefficients TB
      (bitSize (Lax109476.RationalEncoding.encodeProgram (program I layers)))
      (Lax109476.RationalEncoding.encodeProgram (program I layers)).length ≤ (timeBound p coefficients TB).eval L := by
  let L := bitSize (encodeInput kind I)
  let s := bitSize (Lax109476.RationalEncoding.encodeProgram (program I layers))
  let S := LayeredLpSize.sizeBound.eval L
  have hs : s ≤ S := LayeredLpSize.polynomial_size kind I layers hlayers
  have hlen : (Lax109476.RationalEncoding.encodeProgram (program I layers)).length ≤ S :=
    (WordSize.length_le _).trans hs
  have hT : TB.eval s ≤ TB.eval S := eval_mono TB hs
  have hsize : (12*s+39)*(Lax109476.RationalEncoding.encodeProgram (program I layers)).length ≤ (12*S+39)*S :=
    Nat.mul_le_mul (by omega) hlen
  have hsimulation : (TB.eval s+1)*(4*p.length+32*TB.eval s+104) ≤
      (TB.eval S+1)*(4*p.length+32*TB.eval S+104) := Nat.mul_le_mul (by omega) (by omega)
  have hword : LayeredLpSize.wordLength n layers ≤ S := by
    rw [←LayeredLpSize.program_length I]
    exact hlen
  have hbuild : RamLayeredLp.cost n layers ≤ 300*S+34 := by
    dsimp only [RamLayeredLp.cost,LayeredLpSize.wordLength] at *
    omega
  change RamLayeredLp.cost n layers+RamFlowLpSolver.invocationCost p coefficients TB s
    (Lax109476.RationalEncoding.encodeProgram (program I layers)).length ≤ (timeBound p coefficients TB).eval L
  rw [timeBound_eval]
  dsimp only [RamFlowLpSolver.invocationCost]
  dsimp only [S] at hsize hsimulation
  omega

end Lax455465Proofs.RamLayeredSolverBounds
