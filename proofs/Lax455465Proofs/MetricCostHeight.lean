import Lax455465Proofs.MetricCostData
import Lax455465Proofs.RationalSumHeight

namespace Lax455465Proofs.MetricCostHeight

open Lax455465.RationalEncoding LpInputSize MetricMatrix
open scoped NNRat

def exponent (n L K : ℕ) : ℕ := (L+K)*(n*n+1)+n*n+1

/-- Products use only one input capacity and one computed distance. -/
theorem products_height {n : ℕ} (kind : Lax455465.ProductNetwork.EdgeKind) (I : RationalInstance n)
    (d : Matrix n) (K : ℕ) (hd : ∀ u v, Height (2^K) (d u v : ℚ)) :
    ∀ q ∈ RamProductSum.products (values I.capacity) (values d),
      Height (2^(Lax759944.BinaryWordEncoding.bitSize (encodeInput kind I)+K)) (q : ℚ) := by
  rw [MetricCostData.products_eq]
  intro q hq
  obtain ⟨e,rfl⟩ := List.mem_ofFn.mp hq
  let uv := (DirectedFlowLP.edgeIndex n).symm e
  have h := height_mul (capacity_height kind I uv.1 uv.2) (hd uv.1 uv.2)
  rw [←Nat.pow_add] at h
  exact h

/-- Every accumulated metric cost remains on a polynomial-height
common-denominator lattice. -/
theorem prefix_height {n : ℕ} (kind : Lax455465.ProductNetwork.EdgeKind) (I : RationalInstance n)
    (d : Matrix n) (K : ℕ) (hd : ∀ u v, Height (2^K) (d u v : ℚ)) (i : ℕ) :
    Height (2^(exponent n (Lax759944.BinaryWordEncoding.bitSize (encodeInput kind I)) K))
      ((((RamProductSum.products (values I.capacity) (values d)).take i).sum : ℚ≥0) : ℚ) := by
  have hh := products_height kind I d K hd
  have hnum : ∀ q ∈ RamProductSum.products (values I.capacity) (values d),
      q.num ≤ 2^(Lax759944.BinaryWordEncoding.bitSize (encodeInput kind I)+K) := by
    intro q hq
    simpa only [NNRat.natAbs_num_coe] using (hh q hq).1
  have hden : ∀ q ∈ RamProductSum.products (values I.capacity) (values d),
      q.den ≤ 2^(Lax759944.BinaryWordEncoding.bitSize (encodeInput kind I)+K) := by
    intro q hq
    simpa only [NNRat.den_coe] using (hh q hq).2
  simpa only [RamProductSum.products,List.length_ofFn,length_values,exponent] using
    RationalSumHeight.prefix_dyadic_height _ _ hnum hden i

end Lax455465Proofs.MetricCostHeight
