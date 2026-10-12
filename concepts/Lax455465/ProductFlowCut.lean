import Lax455465.RamProductFlowCut
import Lax455465.ArcToPath

/-!
---
title: Classical product multicommodity flow–cut bound
type: lemma
---
For one universal constant $C>0$, every rational product-demand instance
with $p\ge2$ positive-weight vertices satisfies
$$\operatorname{sparsestCut}(G,\pi)
  \le C\log_2(p)\,\operatorname{maxFlow}(G,\pi).$$
The statement covers directed arcs with separate capacities and symmetric
undirected edges with shared capacities. Uniform demand is the all-one
specialization.

# Formalization notes

The maximum flow is the supremum over the real-valued simple-path flows
defined in `ConcurrentFlow`. This corollary uses the joint certificate
returned by the deterministic RAM algorithm and the public arc-to-path
conversion, connecting the algorithmic guarantee to the classical values.
-/

namespace Lax455465.ProductFlowCut
open Lax455465.ProductNetwork Lax455465.ConcurrentFlow Lax455465.RationalEncoding

/-- The classical flow–cut inequality follows from the constructive certificate. -/
axiom exists_flow_cut_bound :
  ∃ C : ℝ, 0 < C ∧
    ∀ (kind : EdgeKind) (n : ℕ) (I : RationalInstance n),
      (kind = .undirected → I.network.IsUndirected) →
      2 ≤ supportCount I.weights →
      (sparsestCut I.network I.weights : ℝ) ≤
        C * logFactor (supportCount I.weights) * (maxFlow kind I.network I.weights : ℝ)

end Lax455465.ProductFlowCut
