import Lax455465Proofs.RamWeightProduct
import Lax455465Proofs.RamFractionPrimitives

namespace Lax455465Proofs.RamFlowDemand

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamVirtualState
open scoped NNRat

/-- At distinct endpoints the flow-value coefficient is a signed product;
it vanishes at all other vertices and for equal-endpoint commodities. -/
def value (s t u : ℕ) (product : ℚ) : ℚ :=
  if s = t then 0 else if u = s then -product else if u = t then product else 0

def command : Com := .ite (.eq (.var "lp.s") (.var "lp.t")) RamFractionPrimitives.zero
  (.ite (.eq (.var "lp.u") (.var "lp.s"))
    (.seq RamWeightProduct.command RamFractionPrimitives.negate)
    (.ite (.eq (.var "lp.u") (.var "lp.t")) RamWeightProduct.command RamFractionPrimitives.zero))

theorem command_spec (B M : ℕ) (weights : List ℚ≥0) (s t u : ℕ)
    (hs : s < weights.length) (ht : t < weights.length) (hu : u < B)
    (hB : 2*M^2+3 < B) (hsi : 2*s+1 < B) (hti : 2*t+1 < B)
    (hsn : weights[s].num ≤ M) (hsd : weights[s].den ≤ M)
    (htn : weights[t].num ≤ M) (htd : weights[t].den ≤ M) :
    Spec B (fun σ => Prefix (RamUnsignedBuffer.encode weights) "flow.weights" σ ∧
      σ.vars "lp.s" = s ∧ σ.vars "lp.t" = t ∧ σ.vars "lp.u" = u) command
      (fun _ τ => FractionOutput (value s t u ((weights[s] : ℚ)*(weights[t] : ℚ))) τ)
      (36*(weights[s].den*weights[t].den).size+120) := by
  have h1 : 1 < B := by nlinarith
  have hsB : s < B := by omega
  have htB : t < B := by omega
  have hproduct := RamWeightProduct.command_spec B M weights s t hs ht hB hsi hti hsn hsd htn htd
  have hneg := RamFractionPrimitives.negate_spec B ((weights[s] : ℚ)*(weights[t] : ℚ)) h1
  have hzero := RamFractionPrimitives.zero_spec B h1
  rintro σ ⟨hp,hσs,hσt,hσu⟩
  run_vcg [hproduct,hneg,hzero]
  all_goals simp_all [value]

end Lax455465Proofs.RamFlowDemand
