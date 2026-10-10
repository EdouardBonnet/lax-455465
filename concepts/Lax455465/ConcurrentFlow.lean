import Lax455465.ProductNetwork
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.List.Count

/-!
---
title: Concurrent fractional flow
type: definition
---
A fractional flow assigns nonnegative amounts to finitely many simple paths.
It is feasible when the total load on every edge is at most its capacity.
Undirected edges carry the sum of the loads in both directions; directed arcs
carry only forward load. A concurrent flow of value $f$ meets $f$ times
every commodity's demand simultaneously. The maximum concurrent flow is the
supremum of feasible values.

# Formalization notes

A path is its ordered vertex list. Positive flow is supported only on lists
with at least two vertices and no repeated vertex. Its commodity is determined
by its endpoints, rather than stored separately. Requiring at least the stated
demand allows excess flow; deleting excess gives the usual equality formulation.
Cycles are unnecessary for fractional routing and can be deleted.

For undirected product demand, each ordered pair receives $f\pi(u)\pi(v)/2$;
for directed product demand it receives $f\pi(u)\pi(v)$. Only distinct
endpoints impose demands. An absent edge has zero capacity, so feasibility
prevents a positive-flow path from using it. There are finitely many simple
paths on `Fin n`; with at least two positive-weight vertices, feasible values
form a nonempty bounded set and the supremum is attained.
-/

open scoped BigOperators NNReal

namespace Lax455465.ConcurrentFlow

open Lax455465.ProductNetwork

/-- A finite assignment of nonnegative flow amounts to vertex lists. -/
abbrev PathFlow (n : ℕ) := List (Fin n) →₀ ℝ≥0

/-- Every path carrying positive flow is simple and has distinct endpoints. -/
def IsPathFlow {n : ℕ} (F : PathFlow n) : Prop :=
  ∀ P ∈ F.support, 2 ≤ P.length ∧ P.Nodup

/-- The forward load on an arc, counting its occurrences on each path. -/
noncomputable def arcLoad {n : ℕ} (F : PathFlow n) (u v : Fin n) : ℝ≥0 :=
  ∑ P ∈ F.support, F P * ((P.zip P.tail).count (u, v) : ℝ≥0)

/-- The capacity consumed by a path flow in the chosen edge model. -/
noncomputable def edgeLoad {n : ℕ} (kind : EdgeKind) (F : PathFlow n)
    (u v : Fin n) : ℝ≥0 :=
  match kind with
  | .undirected => arcLoad F u v + arcLoad F v u
  | .directed => arcLoad F u v

/-- The amount routed from one endpoint to another. -/
noncomputable def routed {n : ℕ} (F : PathFlow n) (s t : Fin n) : ℝ≥0 :=
  ∑ P ∈ F.support,
    if P.head? = some s ∧ P.getLast? = some t then F P else 0

/-- The demand assigned to an ordered pair of distinct endpoints. -/
noncomputable def pairDemand {n : ℕ} (kind : EdgeKind) (π : VertexWeight n)
    (s t : Fin n) : ℝ≥0 :=
  match kind with
  | .undirected => π s * π t / 2
  | .directed => π s * π t

/-- A simple-path flow respects capacities and meets the specified common
fraction of every demand. -/
def IsConcurrentFlow {n : ℕ} (kind : EdgeKind) (N : Network n)
    (π : VertexWeight n) (f : ℝ≥0) (F : PathFlow n) : Prop :=
  IsPathFlow F ∧
    (∀ u v, edgeLoad kind F u v ≤ N.capacity u v) ∧
      ∀ s t, s ≠ t → f * pairDemand kind π s t ≤ routed F s t

/-- The largest feasible concurrent-flow value, expressed as a supremum. -/
noncomputable def maxFlow {n : ℕ} (kind : EdgeKind) (N : Network n)
    (π : VertexWeight n) : ℝ≥0 :=
  sSup {f | ∃ F : PathFlow n, IsConcurrentFlow kind N π f F}

end Lax455465.ConcurrentFlow
