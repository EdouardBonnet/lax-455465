import Lax455465Proofs.DirectedFlowBounds

namespace Lax455465Proofs.FlowOptimalCertificate

open Lax455465.ProductNetwork Lax455465.RationalEncoding DirectedFlowLP
open Lax109476.LinearProgram Lax109476.RationalCertificates

/-- A certificate returned for a nontrivial flow instance is necessarily
optimal. This statement uses the actual certificate, without a second call
to the abstract solver. -/
theorem optimal {n : ℕ} (I : RationalInstance n)
    (hp : 2 ≤ supportCount I.weights)
    (certificate : Certificate (n*n+2*((n*n)*n)) (1+(n*n)*(n*n)))
    (hvalid : IsValidCertificate (program I) certificate) :
    ∃ z y, certificate = .optimal z y ∧ PrimalFeasible (program I) z ∧
      DualFeasible (program I) y ∧ primalValue (program I) z = dualValue (program I) y := by
  cases certificate with
  | optimal z y => exact ⟨z,y,rfl,hvalid⟩
  | infeasible y => exact False.elim (DirectedFlowBounds.no_infeasibility_certificate I y hvalid)
  | unbounded z d => exact False.elim (DirectedFlowBounds.no_improving_direction I hp d hvalid.2)

end Lax455465Proofs.FlowOptimalCertificate
