import Lax455465Proofs.InstanceParser
import Lax455465Proofs.LpCertificateParser
import Lax455465Proofs.CertificatePostprocessing
import Lax109476.PolynomialTimeSolver

namespace Lax455465Proofs.FlowCutProgram

open Lax455465.RationalEncoding Lax455465.ProductNetwork Lax455465.FlowCutCertificate
open DirectedFlowLP

/-- Dense flow-LP reduction applied to the actual decoded input word. -/
def lpInput (input : List ℕ) : List ℕ :=
  match InstanceParser.input input with
  | none => []
  | some data => Lax109476.RationalEncoding.encodeProgram (program data.data)

/-- Parse the solver's exact witnesses and emit the joint cut/flow output.
Malformed outputs and impossible LP outcomes yield the empty word. -/
def finish (data : InstanceParser.Decoded) (lpOutput : List ℕ) : List ℕ :=
  match LpCertificateParser.certificate (data.order * data.order + 2 * ((data.order * data.order) * data.order))
      (1 + (data.order * data.order) * (data.order * data.order)) lpOutput with
  | some (certificate, []) =>
      match CertificatePostprocessing.process data.kind data.data certificate with
      | none => []
      | some output => encodeCertificate output
  | _ => []

/-- The whole deterministic word transformation, parameterized by a
registered LP solver function. No optimizer or witness enters the input. -/
def solve (lpSolve : List ℕ → List ℕ) (input : List ℕ) : List ℕ :=
  match InstanceParser.input input with
  | none => []
  | some data => finish data (lpSolve (Lax109476.RationalEncoding.encodeProgram (program data.data)))

/-- Functional correctness includes the exact output word and witnesses
checked against the original instance. Resource bounds remain a separate
implementation obligation. -/
theorem solve_correct (lpSolve : List ℕ → List ℕ)
    (hsolve : ∀ (m n : ℕ) (P : Lax109476.LinearProgram.Program ℚ m n),
      ∃ certificate : Lax109476.RationalCertificates.Certificate m n,
        lpSolve (Lax109476.RationalEncoding.encodeProgram P) =
          Lax109476.RationalEncoding.encodeCertificate certificate ∧
        Lax109476.RationalCertificates.IsValidCertificate P certificate)
    {n : ℕ} (kind : EdgeKind) (I : RationalInstance n)
    (hsym : kind = .undirected → I.network.IsUndirected) (hp : 2 ≤ supportCount I.weights) :
    ∃ output, solve lpSolve (encodeInput kind I) = encodeCertificate output ∧
      IsValid kind I 512 output := by
  obtain ⟨certificate, hword, hvalid⟩ := hsolve _ _ (program I)
  obtain ⟨output, houtput, hgood⟩ := CertificatePostprocessing.process_correct kind I certificate hvalid hsym hp
  have hparse := LpCertificateParser.certificate_encode certificate []
  simp only [List.append_nil] at hparse
  refine ⟨output, ?_, hgood⟩
  simp only [solve, InstanceParser.input_encode, finish, hword, hparse, houtput]

/-- One LP function works for every flow instance. Its public RAM theorem
is retained for composition with the native host implementation. -/
theorem exists_uniform_word_solver :
    ∃ lpSolve : List ℕ → List ℕ, Lax759944.RamPolytime.RamPolytime lpSolve ∧
      ∀ (kind : EdgeKind) (n : ℕ) (I : RationalInstance n),
        (kind = .undirected → I.network.IsUndirected) → 2 ≤ supportCount I.weights →
        ∃ output, solve lpSolve (encodeInput kind I) = encodeCertificate output ∧ IsValid kind I 512 output := by
  obtain ⟨lpSolve, htime, hsolve⟩ := Lax109476.PolynomialTimeSolver.exists_exact_polynomial_time_solver
  exact ⟨lpSolve, htime, fun kind _ I hsym hp => solve_correct lpSolve hsolve kind I hsym hp⟩

end Lax455465Proofs.FlowCutProgram
