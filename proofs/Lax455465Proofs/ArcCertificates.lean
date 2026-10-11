import Lax455465Proofs.DirectedFlowBounds

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators NNRat NNReal

namespace Lax455465Proofs.ArcCertificates

open Lax455465.ProductNetwork Lax455465.ConcurrentFlow Lax455465.RationalEncoding
open Lax455465Proofs.DirectedFlowLP Lax455465Proofs.DirectedFlowBounds

/-- Use the proved nonnegative LP coordinates as exact rational certificate fields. -/
def certificate {n : ℕ} (I : RationalInstance n) (f : ℚ)
    (x : CommodityArc n → ℚ) (_h : Feasible I f x) : ArcCertificate n where
  value := f.toNNRat
  arcs s t u v := (x ((s, t), (u, v))).toNNRat

private theorem cast_rational (q : ℚ≥0) :
    ((q : ℝ≥0) : ℝ) = ((q : ℚ) : ℝ) := by
  change (NNRat.cast q : ℝ) = ((q : ℚ) : ℝ)
  exact (Rat.cast_nnratCast q).symm

/-- The exact rational edge-LP constraints imply the real directed-flow specification. -/
theorem certificate_valid {n : ℕ} (I : RationalInstance n) (f : ℚ)
    (x : CommodityArc n → ℚ) (h : Feasible I f x) :
    IsArcConcurrentFlow .directed I.network I.weights
      ((certificate I f x h).value : ℝ≥0) (certificate I f x h).flow := by
  have hvalue : (((certificate I f x h).value : ℝ≥0) : ℝ) = (f : ℝ) := by
    rw [cast_rational]
    simp [certificate, Rat.coe_toNNRat f h.1]
  have harcs : ∀ s t u v, ((certificate I f x h).flow s t u v : ℝ) =
      (x ((s, t), (u, v)) : ℝ) := by
    intro s t u v
    change (((x ((s, t), (u, v))).toNNRat : ℝ≥0) : ℝ) = _
    rw [cast_rational, Rat.coe_toNNRat _ (h.2.1 _)]
  constructor
  · intro u v
    apply NNReal.coe_le_coe.mp
    simp only [totalEdgeLoad, totalArcLoad, NNReal.coe_sum, harcs,
      RationalInstance.network, cast_rational]
    have hcap := h.2.2.1 (u, v)
    have hR : (∑ st : Edge n, (x (st, (u, v)) : ℝ)) ≤
        ((I.capacity u v : ℚ) : ℝ) := by exact_mod_cast hcap
    simpa only [Fintype.sum_prod_type] using hR
  · intro s t u
    have hbal := h.2.2.2 (s, t) u
    have hR : (∑ v, (x ((s, t), (u, v)) : ℝ)) -
        (∑ v, (x ((s, t), (v, u)) : ℝ)) =
        (f : ℝ) * (divergence I s t u : ℝ) := by exact_mod_cast hbal
    simp only [harcs]
    rw [hR]
    simp only [divergence, requiredSupply, pairDemand]
    split_ifs <;> simp [NNReal.coe_mul, hvalue, RationalInstance.weights,
      cast_rational, Rat.cast_nnratCast] <;> ring

/-- The actual LP solver supplies an exact rational directed-flow witness and
matching dual multipliers, before the cut-rounding stage. -/
theorem exact_flow_and_dual {n : ℕ} (I : RationalInstance n)
    (hp : 2 ≤ supportCount I.weights) :
    ∃ (F : ArcCertificate n)
      (y : Fin (n * n + 2 * ((n * n) * n)) → ℚ),
      IsArcConcurrentFlow .directed I.network I.weights (F.value : ℝ≥0) F.flow ∧
      Lax109476.LinearProgram.DualFeasible (program I) y ∧
      (F.value : ℚ) = Lax109476.LinearProgram.dualValue (program I) y := by
  obtain ⟨f, x, y, h, hy, heq⟩ := exact_optimal_pair I hp
  refine ⟨certificate I f x h, y, certificate_valid I f x h, hy, ?_⟩
  simpa only [certificate, Rat.coe_toNNRat f h.1] using heq

end Lax455465Proofs.ArcCertificates
