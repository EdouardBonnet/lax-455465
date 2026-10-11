import Lax455465Proofs.RamFlowLpSolver
import Lax455465Proofs.RamFlowLpBounds
import Lax455465Proofs.LpInputSize

namespace Lax455465Proofs.RamFlowSolverBounds

open Lax759944.BinaryWordEncoding Lax455465.RationalEncoding DirectedFlowLP

/-- Evaluation of a polynomial with natural coefficients is monotone. -/
theorem eval_mono (p : Polynomial ℕ) {x y : ℕ} (h : x ≤ y) : p.eval x ≤ p.eval y := by
  obtain ⟨coefficients,hcoeff⟩ := RamPolynomial.exists_coefficients p
  rw [←hcoeff x,←hcoeff y]
  exact RamPolynomial.value_mono coefficients h

noncomputable def timeBound (p : Lax808846.Ram.Program) (coefficients : List ℕ) (TB : Polynomial ℕ) : Polynomial ℕ :=
  let S := LpInputSize.sizeBound
  let T := TB.comp S
  Polynomial.C 10000*(Polynomial.X+Polynomial.C 1)^8 +
    (Polynomial.C 12*S+Polynomial.C 39)*S+Polynomial.C (6*coefficients.length+29)+
    (T+Polynomial.C 1)*(Polynomial.C (4*p.length+104)+Polynomial.C 32*T)+Polynomial.C 18

theorem timeBound_eval (p : Lax808846.Ram.Program) (coefficients : List ℕ) (TB : Polynomial ℕ) (L : ℕ) :
    (timeBound p coefficients TB).eval L = 10000*(L+1)^8+
      (12*LpInputSize.sizeBound.eval L+39)*LpInputSize.sizeBound.eval L+6*coefficients.length+29+
      (TB.eval (LpInputSize.sizeBound.eval L)+1)*(4*p.length+32*TB.eval (LpInputSize.sizeBound.eval L)+104)+18 := by
  simp [timeBound,Polynomial.eval_comp]
  ring

/-- Construction, runtime size measurement, framing and the complete
registered LP execution have one polynomial instruction bound in the
original flow input size. The source program and both polynomials are fixed. -/
theorem cost_bound (p : Lax808846.Ram.Program) (coefficients : List ℕ) (TB : Polynomial ℕ)
    {n : ℕ} (kind : Lax455465.ProductNetwork.EdgeKind) (I : RationalInstance n) :
    let L := bitSize (encodeInput kind I)
    RamFlowLp.cost n (2^L)+RamFlowLpSolver.invocationCost p coefficients TB
      (bitSize (Lax109476.RationalEncoding.encodeProgram (program I)))
      (Lax109476.RationalEncoding.encodeProgram (program I)).length ≤ (timeBound p coefficients TB).eval L := by
  let L := bitSize (encodeInput kind I)
  let s := bitSize (Lax109476.RationalEncoding.encodeProgram (program I))
  let S := LpInputSize.sizeBound.eval L
  have hs : s ≤ S := LpInputSize.flow_program_polynomial_size kind I
  have hlen : (Lax109476.RationalEncoding.encodeProgram (program I)).length ≤ S :=
    (WordSize.length_le _).trans hs
  have hT : TB.eval s ≤ TB.eval S := eval_mono TB hs
  have hsize : (12*s+39)*(Lax109476.RationalEncoding.encodeProgram (program I)).length ≤ (12*S+39)*S :=
    Nat.mul_le_mul (by omega) hlen
  have hsimulation : (TB.eval s+1)*(4*p.length+32*TB.eval s+104) ≤
      (TB.eval S+1)*(4*p.length+32*TB.eval S+104) := Nat.mul_le_mul (by omega) (by omega)
  have hbuild := RamFlowLpBounds.cost_bound n L (LpInputSize.input_dimension kind I)
  change RamFlowLp.cost n (2^L)+RamFlowLpSolver.invocationCost p coefficients TB s
    (Lax109476.RationalEncoding.encodeProgram (program I)).length ≤ (timeBound p coefficients TB).eval L
  rw [timeBound_eval]
  dsimp only [RamFlowLpSolver.invocationCost]
  dsimp only [S] at hsize hsimulation
  omega

end Lax455465Proofs.RamFlowSolverBounds
