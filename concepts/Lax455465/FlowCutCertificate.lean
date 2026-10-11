import Lax455465.RationalEncoding

/-!
---
title: Exact flow–cut output certificates
type: definition
---
The output contains both a cut and a rational concurrent flow. For a product
instance with $p$ positive-weight vertices, the cut has positive demand, the
flow is feasible, and their values satisfy
$$\operatorname{ratio}(S)\le C\log_2(p)\,f.$$
The same output witnesses both sides of the algorithmic flow–cut guarantee.
A zero-capacity cut and the zero flow are valid when the instance has no
positive concurrent flow.

# Formalization notes

The output starts with the length-$n$ cut membership word, followed by the
existing rational arc-flow encoding. Validity is checked against the input;
an output annotation about its approximation ratio is never trusted.
-/

open scoped NNReal

namespace Lax455465.FlowCutCertificate

open Lax455465.ProductNetwork Lax455465.ConcurrentFlow Lax455465.RationalEncoding

/-- The cut and rational path flow returned by a flow–cut algorithm. -/
structure Certificate (n : ℕ) where
  /-- One shore of the cut. -/
  cut : Finset (Fin n)
  /-- A concurrent flow with an explicitly claimed value. -/
  flow : ArcCertificate n

/-- The exact output contains the cut followed by the flow certificate. -/
def encodeCertificate {n : ℕ} (certificate : Certificate n) : List ℕ :=
  encodeCut certificate.cut ++ encodeArcs certificate.flow

/-- The joint guarantee for directed and undirected product demands. -/
def IsValid {n : ℕ} (kind : EdgeKind) (I : RationalInstance n) (C : ℝ)
    (certificate : Certificate n) : Prop :=
  AdmissibleCut I.weights certificate.cut ∧
  IsArcConcurrentFlow kind I.network I.weights
    (certificate.flow.value : ℝ≥0) certificate.flow.flow ∧
  (ratioCost I.network I.weights certificate.cut : ℝ) ≤
    C * logFactor (supportCount I.weights) * (certificate.flow.value : ℝ)

end Lax455465.FlowCutCertificate
