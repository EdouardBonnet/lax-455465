import Lax455465.ConcurrentFlow

/-!
---
title: Concurrent flow on short paths
type: definition
---
The length of a path is its number of edges. A fractional flow has path
length at most $L$ if every path carrying positive flow has at most $L$
edges. For an undirected network, $C_{\max}$ is the largest total capacity
incident to a single vertex.

# Formalization notes

Path lengths are integers, compared with a real bound. Only the support
of the fractional flow matters. Incident capacity sums the capacity matrix
along one row, counting each edge incident to the vertex once.
-/

open scoped BigOperators NNReal

namespace Lax455465.ShortPathFlow

open Lax455465.ProductNetwork Lax455465.ConcurrentFlow

/-- Every path carrying flow has at most `L` edges. -/
def HasPathLengthAtMost {n : ℕ} (F : PathFlow n) (L : ℝ) : Prop :=
  ∀ P ∈ F.support, ((P.length - 1 : ℕ) : ℝ) ≤ L

/-- The largest total capacity incident to one vertex. -/
noncomputable def maxIncidentCapacity {n : ℕ} (N : Network n) : ℝ≥0 :=
  sSup {r | ∃ v : Fin n, (∑ u : Fin n, N.capacity v u) = r}

end Lax455465.ShortPathFlow
