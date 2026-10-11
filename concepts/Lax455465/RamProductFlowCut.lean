import Lax455465.FlowCutCertificate

/-!
---
title: Deterministic polynomial-time product flow–cut algorithm
type: theorem
---
One deterministic polynomial-time word-RAM algorithm returns a rational
concurrent flow and a positive-demand cut for every rational product-demand
instance with $p\ge2$ positive-weight vertices. Their values satisfy
$$\operatorname{ratio}(S)\le C\log_2(p)\,f$$
for one universal constant $C>0$. The input may have directed arcs with
asymmetric capacities, or undirected edges with shared capacities.

# Formalization notes

This is the constructive form of Theorems 7 and 17 of Leighton and Rao
(1999). Zero-weight transit vertices and arbitrary rational capacities and
weights are allowed. Uniform instances and the two edge models are
specializations of this single statement. The edge model is supplied in the
input encoding; its symmetry hypothesis applies to undirected instances.

The algorithm returns the exact joint certificate. The registered
`RamPolytime` predicate certifies a single deterministic program, measured
in binary input size, at every sufficiently large word length. Neither the
LP solution nor the rounding step is an assumed computational oracle.
-/

namespace Lax455465.RamProductFlowCut

open Lax455465.ProductNetwork Lax455465.RationalEncoding Lax455465.FlowCutCertificate
open Lax759944.RamPolytime

/-- A uniform deterministic RAM constructs a logarithmic flow–cut certificate. -/
axiom exists_polynomial_time_flow_cut :
  ∃ (solve : List ℕ → List ℕ) (C : ℝ), RamPolytime solve ∧ 0 < C ∧
    ∀ (kind : EdgeKind) (n : ℕ) (I : RationalInstance n),
      (kind = .undirected → I.network.IsUndirected) →
      2 ≤ supportCount I.weights →
      ∃ certificate : Certificate n,
        solve (encodeInput kind I) = encodeCertificate certificate ∧
        IsValid kind I C certificate

end Lax455465.RamProductFlowCut
