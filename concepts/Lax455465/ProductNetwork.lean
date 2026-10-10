import Mathlib.Data.Finset.Powerset
import Mathlib.Data.NNReal.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
---
title: Product multicommodity networks and sparsest cuts
type: definition
---
A product multicommodity network has nonnegative edge capacities and a
nonnegative weight $\pi(v)$ at each vertex. In an undirected network, the
demand between distinct vertices $u,v$ is $\pi(u)\pi(v)$, shared equally
between the two directions. In a directed network, the demand from $u$ to $v$
is $\pi(u)\pi(v)$ in each direction separately. Uniform demands are the case
$\pi\equiv1$.

The ratio cost of a cut $(S,\overline S)$ is
$$\frac{C(S,\overline S)}{\pi(S)\pi(\overline S)}.$$
Its numerator counts each undirected crossing edge once, or only arcs leaving
$S$ in the directed case. The sparsest-cut value is the infimum of these
ratios over cuts of positive demand. Write $p$ for the number of vertices
of positive weight.

# Formalization notes

Vertices are `Fin n`. A capacity matrix represents parallel edges by their
total capacity and absent edges by zero; loops are excluded. An undirected
network has a symmetric capacity matrix. The same cut formula applies in
both cases. Cuts of zero demand are excluded, including empty cuts. When
$p\ge2$, the set of admissible cuts is finite and nonempty, so its infimum
is a minimum. The theorems impose this hypothesis explicitly.

The logarithmic factor is $\log_2 p$, as in the paper. Stating product
bounds in terms of $p$ also handles the two-terminal case, where the
paper's shorthand $\log k$ vanishes because $k=\binom p2=1$.
-/

open scoped BigOperators NNReal

namespace Lax455465.ProductNetwork

/-- Whether capacities are shared by both directions of an edge or belong
to individual directed arcs. -/
inductive EdgeKind
  /-- One capacity shared by both directions of an undirected edge. -/
  | undirected
  /-- A separate capacity for each directed arc. -/
  | directed
  deriving DecidableEq

/-- A finite loopless network with nonnegative capacities. -/
structure Network (n : ℕ) where
  /-- The capacity of an edge or arc, with zero denoting absence. -/
  capacity : Fin n → Fin n → ℝ≥0
  /-- Loops are absent. -/
  loopless : ∀ v, capacity v v = 0

/-- An undirected network has the same capacity in both directions. -/
def Network.IsUndirected {n : ℕ} (N : Network n) : Prop :=
  ∀ u v, N.capacity u v = N.capacity v u

/-- The nonnegative weights whose products specify the demands. -/
abbrev VertexWeight (n : ℕ) := Fin n → ℝ≥0

/-- The number of vertices with positive weight. -/
noncomputable def supportCount {n : ℕ} (π : VertexWeight n) : ℕ :=
  (Finset.univ.filter fun v => 0 < π v).card

/-- The total vertex weight in a set. -/
def mass {n : ℕ} (π : VertexWeight n) (S : Finset (Fin n)) : ℝ≥0 :=
  ∑ v ∈ S, π v

/-- A cut separates positive total weight on both sides. -/
def AdmissibleCut {n : ℕ} (π : VertexWeight n) (S : Finset (Fin n)) : Prop :=
  0 < mass π S ∧ 0 < mass π Sᶜ

/-- The capacity leaving a cut; symmetric capacities count an undirected
edge exactly once. -/
def cutCapacity {n : ℕ} (N : Network n) (S : Finset (Fin n)) : ℝ≥0 :=
  ∑ u ∈ S, ∑ v ∈ Sᶜ, N.capacity u v

/-- The ratio of cut capacity to separated product demand. -/
noncomputable def ratioCost {n : ℕ} (N : Network n) (π : VertexWeight n)
    (S : Finset (Fin n)) : ℝ≥0 :=
  cutCapacity N S / (mass π S * mass π Sᶜ)

/-- The least ratio cost of a cut with positive demand. -/
noncomputable def sparsestCut {n : ℕ} (N : Network n) (π : VertexWeight n) : ℝ≥0 :=
  sInf {r | ∃ S : Finset (Fin n), AdmissibleCut π S ∧ ratioCost N π S = r}

/-- The all-one vertex weights defining uniform demand. -/
def uniformWeight (n : ℕ) : VertexWeight n := fun _ => 1

/-- The paper's base-two logarithm. -/
noncomputable def logFactor (p : ℕ) : ℝ := Real.log (p : ℝ) / Real.log 2

end Lax455465.ProductNetwork
