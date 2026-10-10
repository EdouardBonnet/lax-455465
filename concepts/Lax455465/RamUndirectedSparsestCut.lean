import Lax455465.RationalEncoding

/-!
---
title: Polynomial-time RAM construction of an undirected sparse cut
type: theorem
---
There is a polynomial-time word-RAM algorithm and a universal constant $C>0$
such that, on every rational undirected product instance with $p\ge2$
positive-weight vertices, the algorithm returns a cut of positive demand with
ratio cost at most $C\log_2(p)f^*$.

Since $f^*\le\mathcal S$, this is also an $O(\log p)$ approximation
algorithm for product sparsest cut, including uniform sparsest cut.

# Formalization notes

This is the constructive guarantee of Sections 2.2–2.3 and 3.1 of Leighton
and Rao (1999). The output must equal the membership word of the witnessing
cut; neither its capacity nor its approximation ratio is trusted as an output
annotation. Polynomial time uses the registered RAM predicate in binary input
size. One algorithm and one approximation constant work for all instances.
-/

namespace Lax455465.RamUndirectedSparsestCut

open Lax455465.ProductNetwork Lax455465.ConcurrentFlow Lax455465.RationalEncoding
open Lax759944.RamPolytime

/-- A polynomial-time RAM returns an undirected cut within the logarithmic
factor of the concurrent-flow optimum. -/
axiom exists_polynomial_time_sparse_cut :
  ∃ (solve : List ℕ → List ℕ) (C : ℝ), RamPolytime solve ∧ 0 < C ∧
    ∀ (n : ℕ) (I : RationalInstance n),
      I.network.IsUndirected → 2 ≤ supportCount I.weights →
        ∃ S : Finset (Fin n),
          solve (encodeInput .undirected I) = encodeCut S ∧
          AdmissibleCut I.weights S ∧
          (ratioCost I.network I.weights S : ℝ) ≤
            C * logFactor (supportCount I.weights) *
              (maxFlow .undirected I.network I.weights : ℝ)

end Lax455465.RamUndirectedSparsestCut
