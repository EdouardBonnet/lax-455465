import Lax455465.RamProductFlowCut
import Lax455465Proofs.RamValidCompilation
import Lax455465Proofs.RamClockPolynomial

namespace Lax455465Proofs.RamProductAlgorithm
open Lax455465.ProductNetwork Lax455465.RationalEncoding Lax455465.FlowCutCertificate
open Lax759944.RamPolytime Lax759944.BinaryWordEncoding

/--
---
conclusion: Lax455465.RamProductFlowCut.exists_polynomial_time_flow_cut
---
One fixed RAM program constructs the joint flow–cut certificate in both
edge models, with universal approximation constant 512.

# Proof strategy

Compile the complete valid-input pipeline: the registered exact LP solver,
rational directed distances, deterministic metric rounding, and certificate
output. A bounded interpreter computes the source word width and clock from
the actual binary input size. Its execution and polynomial resource proofs
apply to every input word. On valid networks its clock contains the complete
source execution, so it emits exactly the certified output. Compiler transfer
establishes the existing uniform word-RAM predicate at every sufficient host
word width.
-/
theorem exists_polynomial_time_flow_cut :
  ∃ (solve : List ℕ → List ℕ) (C : ℝ), RamPolytime solve ∧ 0 < C ∧
    ∀ (kind : EdgeKind) (n : ℕ) (I : RationalInstance n),
      (kind = .undirected → I.network.IsUndirected) →
      2 ≤ supportCount I.weights →
      ∃ certificate : Certificate n,
        solve (encodeInput kind I) = encodeCertificate certificate ∧
        IsValid kind I C certificate := by
  obtain ⟨p,WB,TB,hvalid⟩ := RamValidCompilation.exists_program
  refine ⟨RamClockPolynomial.solve p WB TB,512,RamClockPolynomial.polynomial_time p WB TB,by norm_num,?_⟩
  intro kind n I hsym hp
  obtain ⟨cert,hcert,hrun⟩ := hvalid kind I hsym hp
  obtain ⟨t,ht,hr⟩ := hrun (WB.eval (bitSize (encodeInput kind I))) le_rfl
  obtain ⟨k,hk,s,hs,hstop,hout,_⟩ := SparseRam.exists_execution _ p _ _ t hr
  have he := SparseClock.agrees _ p k (TB.eval (bitSize (encodeInput kind I))) _ s (hk.trans ht) hs hstop
  exact ⟨cert,by simpa only [RamClockPolynomial.solve,he] using hout,hcert⟩

end Lax455465Proofs.RamProductAlgorithm
