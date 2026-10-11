import Lax455465Proofs.SparseRam
import Lax109476.PolynomialTimeSolver

namespace Lax455465Proofs.RegisteredLpExecution

open Lax109476.LinearProgram Lax109476.RationalCertificates Lax109476.RationalEncoding
open Lax759944.BinaryWordEncoding Lax759944.RamPolytime

/-- The registered LP interface supplies one fixed virtual RAM program
and polynomial bounds. Its exact sparse output encodes the same valid
certificate, and its virtual working memory starts at zero. -/
theorem exists_program :
    ∃ (p : Lax808846.Ram.Program) (wordBound timeBound : Polynomial ℕ),
      ∀ (m n : ℕ) (P : Program ℚ m n), ∃ certificate : Certificate m n,
        IsValidCertificate P certificate ∧
        FitsInWords (wordBound.eval (bitSize (encodeProgram P)))
          (((encodeProgram P).length :: encodeProgram P) ++ encodeCertificate certificate) ∧
        ∃ k ≤ timeBound.eval (bitSize (encodeProgram P)), ∃ s : SparseRam.SparseState,
          SparseRam.run (wordBound.eval (bitSize (encodeProgram P))) p k
            (SparseRam.init ((encodeProgram P).length :: encodeProgram P)) = some s ∧
          SparseRam.step (wordBound.eval (bitSize (encodeProgram P))) p s = none ∧
          s.out = encodeCertificate certificate ∧ s.memory.length ≤ k := by
  obtain ⟨solve, htime, hcorrect⟩ := Lax109476.PolynomialTimeSolver.exists_exact_polynomial_time_solver
  obtain ⟨p, wordBound, timeBound, hprogram⟩ := SparseRam.polynomial_execution solve htime
  refine ⟨p, wordBound, timeBound, ?_⟩
  intro m n P
  obtain ⟨certificate, hencode, hvalid⟩ := hcorrect m n P
  have hrun := hprogram (encodeProgram P)
  rw [hencode] at hrun
  exact ⟨certificate, hvalid, hrun⟩

end Lax455465Proofs.RegisteredLpExecution
