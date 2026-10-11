import Lax455465Proofs.DualRounding

open scoped BigOperators NNReal NNRat

namespace Lax455465Proofs.CertificatePostprocessing

open Lax455465.RationalEncoding Lax455465.ProductNetwork Lax455465.ConcurrentFlow
open Lax455465.FlowCutCertificate Lax109476.LinearProgram DirectedFlowLP DirectedFlowBounds

/-- Extract the primal coordinates without requiring proof data at runtime. -/
def primalFlow {n : ℕ} (z : Fin (1 + (n * n) * (n * n)) → ℚ) : ArcCertificate n where
  value := (z (variableIndex n (.inl 0))).toNNRat
  arcs s t u v := (z (variableIndex n (.inr ((s, t), (u, v))))).toNNRat

def convertFlow {n : ℕ} (kind : EdgeKind) (F : ArcCertificate n) : ArcCertificate n :=
  match kind with
  | .directed => F
  | .undirected => UndirectedConversion.halve F

/-- Deterministic postprocessing of the exact LP solver's actual output
certificate, including the cut and all concurrent-flow coordinates. -/
def process {n : ℕ} (kind : EdgeKind) (I : RationalInstance n)
    (lp : Lax109476.RationalCertificates.Certificate (n * n + 2 * ((n * n) * n))
      (1 + (n * n) * (n * n))) : Option (Certificate n) :=
  match lp with
  | .optimal z y => (DualRounding.round I y).map fun S => ⟨S, convertFlow kind (primalFlow z)⟩
  | .infeasible _ => none
  | .unbounded _ _ => none

/-- Every valid LP output for the flow reduction yields a joint flow-cut
certificate. The impossible infeasible and unbounded cases are excluded
from the input data, not assumed away by the algorithm. -/
theorem process_correct {n : ℕ} (kind : EdgeKind) (I : RationalInstance n)
    (lp : Lax109476.RationalCertificates.Certificate (n * n + 2 * ((n * n) * n))
      (1 + (n * n) * (n * n)))
    (hvalid : Lax109476.RationalCertificates.IsValidCertificate (program I) lp)
    (hsym : kind = .undirected → I.network.IsUndirected) (hp : 2 ≤ supportCount I.weights) :
    ∃ output, process kind I lp = some output ∧ IsValid kind I 512 output := by
  cases lp with
  | infeasible y => exact False.elim (no_infeasibility_certificate I y hvalid)
  | unbounded z d => exact False.elim (no_improving_direction I hp d hvalid.2)
  | optimal z y =>
    rcases hvalid with ⟨hz, hy, hmatch⟩
    let f := z (variableIndex n (.inl 0))
    let x := fun a => z (variableIndex n (.inr a))
    have hrepr : vector f x = z := vector_representation z
    have hfeasible : Feasible I f x := by
      rw [← hrepr, feasible_iff] at hz
      exact hz
    let F := ArcCertificates.certificate I f x hfeasible
    have hF := ArcCertificates.certificate_valid I f x hfeasible
    have hvalue : (F.value : ℚ) = dualValue (program I) y := by
      rw [← hrepr, objective_value] at hmatch
      simpa only [F, ArcCertificates.certificate, Rat.coe_toNNRat f hfeasible.1] using hmatch
    have hprimal : F = primalFlow z := rfl
    cases kind with
    | directed =>
      obtain ⟨S, hs, houtput⟩ := DualRounding.directed_certificate I F y hy hp hF hvalue
      refine ⟨⟨S, F⟩, ?_, houtput⟩
      simp only [process, hs, Option.map_some, convertFlow, ← hprimal]
    | undirected =>
      obtain ⟨S, hs, houtput⟩ := DualRounding.undirected_certificate I F y hy hp (hsym rfl) hF hvalue
      refine ⟨⟨S, UndirectedConversion.halve F⟩, ?_, houtput⟩
      simp only [process, hs, Option.map_some, convertFlow, ← hprimal]

end Lax455465Proofs.CertificatePostprocessing
