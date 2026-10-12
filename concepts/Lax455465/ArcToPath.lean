import Lax455465.ConcurrentFlow

/-!
---
title: Arc-to-path conversion for concurrent flows
type: lemma
---
Every feasible concurrent arc flow can be replaced by a finite simple-path
flow of the same value. The conversion never increases the load on any
directed arc, so it preserves both separate directed capacities and shared
undirected capacities.

# Formalization notes

Capacities, vertex weights, and flows may be arbitrary nonnegative reals.
Cycles and diagonal commodities can be discarded. No positivity, symmetry,
or rationality assumption is needed for this representation theorem.
-/

open scoped NNReal

namespace Lax455465.ArcToPath
open Lax455465.ProductNetwork Lax455465.ConcurrentFlow

/-- Conservation and capacities in the arc formulation yield the public
simple-path formulation, with no increase in arc load. -/
axiom exists_path_flow {n : ℕ} (kind : EdgeKind) (N : Network n)
    (π : VertexWeight n) (f : ℝ≥0) (F : ArcFlow n)
    (hF : IsArcConcurrentFlow kind N π f F) :
    ∃ P : PathFlow n, IsConcurrentFlow kind N π f P ∧
      ∀ u v, arcLoad P u v ≤ totalArcLoad F u v

end Lax455465.ArcToPath
