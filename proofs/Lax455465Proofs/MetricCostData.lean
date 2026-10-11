import Lax455465Proofs.RamProductSum
import Lax455465Proofs.MetricMatrix
import Lax455465Proofs.RegionRounding
import Mathlib.Data.NNRat.BigOperators

namespace Lax455465Proofs.MetricCostData

open Lax455465.RationalEncoding DirectedFlowLP MetricMatrix
open scoped BigOperators NNRat

def cost {n : ℕ} (I : RationalInstance n) (d : Matrix n) : ℚ≥0 :=
  (RamProductSum.products (values I.capacity) (values d)).sum

theorem products_eq {n : ℕ} (a b : Matrix n) :
    RamProductSum.products (values a) (values b) = values (fun u v => a u v*b u v) := by
  apply List.ext_getElem
  · simp only [RamProductSum.products,List.length_ofFn,length_values]
  · intro i hi hj
    have he : i < n*n := by simpa only [RamProductSum.products,List.length_ofFn,length_values] using hi
    rw [RamProductSum.value_at (values a) (values b) (by simp) i (by simpa using he)]
    simp only [values,List.getElem_ofFn]

theorem coe_cost {n : ℕ} (I : RationalInstance n) (d : Matrix n) :
    (cost I d : ℚ) = RegionRounding.metricCost I (rational d) := by
  unfold cost
  rw [products_eq]
  simp only [values,List.sum_ofFn]
  rw [←Equiv.sum_comp (edgeIndex n)]
  simp only [Equiv.symm_apply_apply,Fintype.sum_prod_type]
  simp only [NNRat.cast_sum,NNRat.coe_mul,RegionRounding.metricCost,RegionVolume.weight,rational]

end Lax455465Proofs.MetricCostData
