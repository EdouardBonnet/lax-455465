import Lax455465Proofs.LayeredExtractionStep
import Lax455465Proofs.PathRecordArithmetic

namespace Lax455465Proofs.LayeredExtractionLoad
open LayeredFlowLP LayeredGraphFlow LayeredWalkState LayeredPathSweep
open scoped NNRat BigOperators

def localLoad {n L : ℕ} (q : Coordinate n L → ℚ≥0) (st : Edge n) (u v : Fin n) : ℚ :=
  ∑ k : Fin L,arc q (st,(k,(u,v)))

def totalLoad {n L : ℕ} (q : Coordinate n L → ℚ≥0) (u v : Fin n) : ℚ :=
  ∑ st : Edge n,localLoad q st u v

theorem nonnegative {n L : ℕ} (q : Coordinate n L → ℚ≥0) (u v : Fin n) : 0≤totalLoad q u v := by
  apply Finset.sum_nonneg
  intro st _
  exact Finset.sum_nonneg fun k _ => (q _).coe_nonneg

theorem local_after {n L : ℕ} (q : Coordinate n L → ℚ≥0) (w : ℚ≥0)
    (st : Edge n) (path : Fin (L+1) → Fin n) (hw : ∀ k,w≤q (edge st path k)) (u v : Fin n) :
    localLoad (after q w st path L) st u v=localLoad q st u v-
      (w : ℚ)*PathCounting.count ((LayeredSweepGraph.raw path).map Prod.snd) u v := by
  rw [localLoad,←LayeredPathProjection.graph_sum_layers,LayeredSweepGraph.graph_after q w st path hw]
  simp only [PathSubtraction.residual,Finset.sum_sub_distrib,←Finset.mul_sum]
  rw [LayeredPathProjection.graph_sum_layers,←LayeredPathProjection.count_map]
  rfl

theorem total_after {n L : ℕ} (q : Coordinate n L → ℚ≥0) (w : ℚ≥0)
    (st : Edge n) (path : Fin (L+1) → Fin n) (hw : ∀ k,w≤q (edge st path k)) (u v : Fin n) :
    totalLoad (after q w st path L) u v=totalLoad q u v-
      (w : ℚ)*PathCounting.count ((LayeredSweepGraph.raw path).map Prod.snd) u v := by
  have he (other : Edge n) : localLoad (after q w st path L) other u v=
      localLoad q other u v-(if other=st then
        (w : ℚ)*PathCounting.count ((LayeredSweepGraph.raw path).map Prod.snd) u v else 0) := by
    by_cases hh : other=st
    · subst other
      simpa only [if_true] using local_after q w st path hw u v
    · simp only [localLoad,LayeredSweepGraph.other_arc q w st other path hh L,if_neg hh,sub_zero]
  unfold totalLoad
  simp_rw [he]
  rw [Finset.sum_sub_distrib]
  simp

theorem usage_sum {n L : ℕ} (q : Coordinate n L → ℚ≥0) (u v : Fin n) (hne : u≠v) :
    (∑ a : Arc n L,usage (u,v) a*arc q a)=totalLoad q u v+totalLoad q v u := by
  simp only [usage,if_neg hne,add_mul,ite_mul,one_mul,zero_mul,
    Finset.sum_add_distrib,Fintype.sum_prod_type,Prod.mk.injEq,ite_and,
    Finset.sum_ite_irrel,Finset.sum_ite_eq',Finset.mem_univ,if_true,totalLoad,localLoad]

/-- Account for every emitted simple path against the exact raw residual
decrement. This is the capacity invariant used by all extraction loops. -/
theorem step_le {n L : ℕ} {q : Coordinate n L → ℚ≥0} {a : ℚ≥0} {st : Edge n}
    {path : Fin (L+1) → Fin n} {ys : List (Fin n)}
    (h : LayeredExtractionStep.Valid q a st path ys) (u v : Fin n) :
    (LayeredExtractionStep.amount q a st path : ℚ)*PathCounting.count ys u v+
      totalLoad (after q (LayeredExtractionStep.amount q a st path) st path L) u v≤totalLoad q u v := by
  rw [total_after _ _ _ _ (LayeredExtractionStep.amount_le q a st path).2]
  have hc : PathCounting.count ys u v≤
      PathCounting.count ((LayeredSweepGraph.raw path).map Prod.snd) u v := by
    unfold PathCounting.count
    exact_mod_cast h.sublist.count_le (u,v)
  have hm := mul_le_mul_of_nonneg_left hc (LayeredExtractionStep.amount q a st path).coe_nonneg
  linarith only [hm]

end Lax455465Proofs.LayeredExtractionLoad
