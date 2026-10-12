import Lax455465.RamUniformShortPathFlow
import Lax455465Proofs.RamShortCompilation
import Lax455465Proofs.RamClockPolynomial

namespace Lax455465Proofs.RamUniformShortPathFlow
open Lax455465.RationalEncoding Lax455465.ProductNetwork Lax455465.ConcurrentFlow Lax455465.ShortPathFlow
open Lax759944.BinaryWordEncoding Lax759944.RamPolytime
open scoped NNReal

/--
---
conclusion: Lax455465.RamUniformShortPathFlow.exists_polynomial_time_short_path_flow
---
One fixed polynomial-time RAM program constructs the rational short-path
flow of Theorem 18, with universal constants 32768 and 8192.

# Proof strategy

The program reads the source graph, computes the maximum incident capacity,
and invokes the registered exact LP solver on successive layered networks.
It implements the stopping test and extracts the selected primal solution
by deterministic positive-path traversal, bottleneck subtraction, and online
cycle erasure. Conservation and capacity invariants certify the actual emitted
records. A common denominator lattice bounds every residual word independently
of the number of updates. The complete execution has polynomial word and
instruction bounds; compiler simulation and a bounded interpreter establish
the registered uniform RAM predicate on every input.
-/
theorem exists_polynomial_time_short_path_flow :
  ∃ (solve : List ℕ → List ℕ) (A B : ℝ),RamPolytime solve ∧ 0<A ∧ 0<B ∧
    ∀ (n : ℕ) (I : RationalInstance n),I.network.IsUndirected → (∀ v,I.weight v=1) → 2≤n →
      0<sparsestCut I.network (uniformWeight n) → ∃ cert : FlowCertificate n,
        solve (encodeInput .undirected I)=encodeFlow cert ∧
        IsConcurrentFlow .undirected I.network (uniformWeight n) (cert.value : ℝ≥0) cert.flow ∧
        (sparsestCut I.network (uniformWeight n) : ℝ)≤A*logFactor n*(cert.value : ℝ) ∧
        HasPathLengthAtMost cert.flow (B*(maxIncidentCapacity I.network : ℝ)*logFactor n /
          ((n : ℝ)*(sparsestCut I.network (uniformWeight n) : ℝ))) := by
  obtain ⟨p,WB,TB,hvalid⟩:=RamShortCompilation.exists_program
  refine ⟨RamClockPolynomial.solve p WB TB,32768,8192,RamClockPolynomial.polynomial_time p WB TB,
    by norm_num,by norm_num,?_⟩
  intro n I hsym hw hn hS
  obtain ⟨cert,hflow,hvalue,hlength,hrun⟩:=hvalid I hsym hw hn hS
  obtain ⟨t,ht,hr⟩:=hrun (WB.eval (bitSize (encodeInput .undirected I))) le_rfl
  obtain ⟨k,hk,s,hs,hstop,hout,_⟩:=SparseRam.exists_execution _ p _ _ t hr
  have he:=SparseClock.agrees _ p k (TB.eval (bitSize (encodeInput .undirected I))) _ s (hk.trans ht) hs hstop
  exact ⟨cert,by simpa only [RamClockPolynomial.solve,he] using hout,hflow,hvalue,hlength⟩

end Lax455465Proofs.RamUniformShortPathFlow
