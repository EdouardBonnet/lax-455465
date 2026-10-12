import Lax455465.FlowCutCertificate

/-!
---
title: Deterministic undirected product flow–cut algorithm
type: lemma
---
A deterministic polynomial-time word RAM returns a cut and a rational
concurrent flow satisfying
$$\operatorname{ratio}(S)\le C\log_2(p)\,f.$$
Both certificates concern the same rational product-demand instance.

# Formalization notes

This specializes the general product flow–cut algorithm to undirected
capacities and demands, retaining its program, exact output, and binary-size
RAM bound. Undirected capacities are symmetric and shared between directions;
directed cuts count outgoing arcs and directed capacities may be asymmetric.
-/

namespace Lax455465.RamUndirectedSparsestCut

open Lax455465.ProductNetwork Lax455465.RationalEncoding Lax455465.FlowCutCertificate
open Lax759944.RamPolytime

/-- The undirected product specialization returns the joint certificate. -/
axiom exists_polynomial_time_sparse_cut :
  ∃ (solve : List ℕ → List ℕ) (C : ℝ), RamPolytime solve ∧ 0 < C ∧
    ∀ (n : ℕ) (I : RationalInstance n),
      I.network.IsUndirected → 2 ≤ supportCount I.weights →
      ∃ certificate : Certificate n,
        solve (encodeInput .undirected I) = encodeCertificate certificate ∧
        IsValid .undirected I C certificate

end Lax455465.RamUndirectedSparsestCut
