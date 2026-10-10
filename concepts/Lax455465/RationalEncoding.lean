import Lax455465.ConcurrentFlow
import Lax759944.RamPolytime
import Mathlib.Data.NNRat.Lemmas

/-!
---
title: Rational flow instances and certificates
type: definition
---
Finite algorithms receive nonnegative rational capacities and vertex weights.
Each rational is encoded by its reduced numerator and positive denominator.
An instance contains its edge model, number of vertices, vertex weights in
vertex order, and full capacity matrix in row order. A cut is encoded by
its length-$n$ membership word. A fractional-flow certificate contains its
claimed value and a list of paths with rational flow amounts.

# Formalization notes

The dense encoding covers arbitrary rational capacities and weights, including
zero weights and absent edges. The first entry distinguishes directed from
undirected instances. Cut entries are exactly zero or one. A flow certificate
starts with the numerator and denominator of its value and the number of
path records; each record contains its vertex-count, vertex list, numerator,
and denominator. Repeated path records contribute their summed amount.

Algorithms use `Lax759944.RamPolytime.RamPolytime` directly. It quantifies
one actual program, polynomial word and instruction bounds in the binary
input size, and exact execution at every sufficiently large word length on
Lax808846's registered word RAM. The physical tape has the length prefix
specified by that predicate. No new machine or abstract cost oracle is used.
The algorithm's function is total; its output on malformed inputs is unconstrained.
-/

open scoped NNReal NNRat

namespace Lax455465.RationalEncoding

open Lax455465.ProductNetwork Lax455465.ConcurrentFlow

/-- A product instance with nonnegative rational capacities and weights. -/
structure RationalInstance (n : ℕ) where
  /-- The rational capacity of each edge or directed arc. -/
  capacity : Fin n → Fin n → ℚ≥0
  /-- Loops have zero capacity. -/
  loopless : ∀ v, capacity v v = 0
  /-- The rational weights specifying product demands. -/
  weight : Fin n → ℚ≥0

/-- Interpret rational capacities as exact nonnegative real capacities. -/
def RationalInstance.network {n : ℕ} (I : RationalInstance n) : Network n where
  capacity u v := (I.capacity u v : ℝ≥0)
  loopless v := by simpa using congrArg (fun q : ℚ≥0 => (q : ℝ≥0)) (I.loopless v)

/-- Interpret rational vertex weights as exact nonnegative real weights. -/
def RationalInstance.weights {n : ℕ} (I : RationalInstance n) : VertexWeight n :=
  fun v => (I.weight v : ℝ≥0)

/-- Encode a nonnegative rational by its canonical numerator and denominator. -/
def encodeRational (q : ℚ≥0) : List ℕ := [q.num, q.den]

/-- Encode the edge model, order, weights, and row-major capacity matrix. -/
def encodeInput {n : ℕ} (kind : EdgeKind) (I : RationalInstance n) : List ℕ :=
  [match kind with | .undirected => 0 | .directed => 1, n] ++
    (List.ofFn I.weight).flatMap encodeRational ++
    (List.ofFn fun u => List.ofFn (I.capacity u)).flatten.flatMap encodeRational

/-- Encode a shore as its length-`n` membership word. -/
def encodeCut {n : ℕ} (S : Finset (Fin n)) : List ℕ :=
  List.ofFn fun v => if v ∈ S then 1 else 0

/-- A finite rational flow certificate, with its claimed concurrent value. -/
structure FlowCertificate (n : ℕ) where
  /-- The common fraction of demand claimed by the certificate. -/
  value : ℚ≥0
  /-- Paths and their flow amounts; duplicate records are added together. -/
  paths : List (List (Fin n) × ℚ≥0)

/-- The exact fractional path flow represented by a certificate. -/
noncomputable def FlowCertificate.flow {n : ℕ} (certificate : FlowCertificate n) :
    PathFlow n :=
  certificate.paths.foldl
    (fun F record => F + Finsupp.single record.1 (record.2 : ℝ≥0)) 0

/-- Encode a certificate's value and its length-prefixed rational path records. -/
def encodeFlow {n : ℕ} (certificate : FlowCertificate n) : List ℕ :=
  encodeRational certificate.value ++ [certificate.paths.length] ++
    certificate.paths.flatMap fun record =>
      [record.1.length] ++ record.1.map Fin.val ++ encodeRational record.2

end Lax455465.RationalEncoding
