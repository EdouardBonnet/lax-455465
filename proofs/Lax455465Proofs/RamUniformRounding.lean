import Lax455465Proofs.RamRoundingResources

namespace Lax455465Proofs.RamUniformRounding
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRegionContext
open Lax455465.RationalEncoding Lax455465.ProductNetwork Lax759944.BinaryWordEncoding
open LpInputSize RamRoundingResources
open scoped NNRat

/-- A polynomial bit bound on the metric yields one polynomial budget for
the original coefficients, metric cost, and every original weight prefix. -/
theorem data_bounds (P : Polynomial ℕ) {n : ℕ} (kind : EdgeKind) (I : RationalInstance n)
    (d : MetricMatrix.Matrix n)
    (hd : ∀ u v,Height (2^(P.eval (bitSize (encodeInput kind I)))) (d u v : ℚ)) :
    let w := (baseBound P).eval (bitSize (encodeInput kind I))
    2*n+4 ≤ w ∧ (∀ v,Height (2^w) (I.weight v : ℚ)) ∧
      (∀ u v,Height (2^w) (I.capacity u v : ℚ)) ∧ (∀ u v,Height (2^w) (d u v : ℚ)) ∧
      Height (2^w) (MetricCostData.cost I d : ℚ) ∧
      ∀ i,Height (2^w) (((List.ofFn I.weight).take i).sum : ℚ) := by
  let L := bitSize (encodeInput kind I)
  let w := (baseBound P).eval L
  have hn : n ≤ L := input_dimension kind I
  have he : w=(RamMetricCostResources.heightBound P).eval L+L*(L+1)+L+1+P.eval L+3*L+8 := by
    simp [w,baseBound]
  have hL : L ≤ w := by omega
  have hP : P.eval L ≤ w := by omega
  have widen {k : ℕ} {q : ℚ} (h : Height (2^k) q) (hk : k ≤ w) : Height (2^w) q :=
    height_mono h (Nat.pow_le_pow_right (by decide) hk)
  refine ⟨show 2*n+4 ≤ w from by omega,fun v => widen (weight_height kind I v) hL,
    fun u v => widen (capacity_height kind I u v) hL,fun u v => widen (hd u v) hP,?_,?_⟩
  · have hc := MetricCostHeight.prefix_height kind I d (P.eval L) hd
      (RamProductSum.products (MetricMatrix.values I.capacity) (MetricMatrix.values d)).length
    have hc' : Height (2^(MetricCostHeight.exponent n L (P.eval L))) (MetricCostData.cost I d : ℚ) := by
      simpa only [List.take_length,MetricCostData.cost] using hc
    apply widen hc'
    have hh := RamMetricCostResources.height_bound P kind I
    change MetricCostHeight.exponent n L (P.eval L) ≤ (RamMetricCostResources.heightBound P).eval L at hh
    omega
  · intro i
    have hw : ∀ q∈List.ofFn I.weight,Height (2^L) (q : ℚ) := by
      intro q hq
      obtain ⟨v,rfl⟩ := List.mem_ofFn.mp hq
      exact weight_height kind I v
    have hs := RationalSumHeight.prefix_dyadic_height (List.ofFn I.weight) L
      (fun q hq => num_bound (hw q hq)) (fun q hq => den_bound (hw q hq)) i
    have hs' : Height (2^(L*(n+1)+n+1)) (((List.ofFn I.weight).take i).sum : ℚ) := by
      simpa only [List.length_ofFn] using hs
    apply widen hs'
    have hm := Nat.mul_le_mul_left L (show n+1 ≤ L+1 by omega)
    omega

/-- A single native rounding command has polynomial time and sufficient
word width in the source graph's binary size. It computes all constants and
uses the original metric buffer; the bit bounds supply no runtime advice. -/
theorem command_spec (P : Polynomial ℕ) {n : ℕ} (kind : EdgeKind) (I : RationalInstance n)
    (d : MetricMatrix.Matrix n)
    (hd : ∀ u v,Height (2^(P.eval (bitSize (encodeInput kind I)))) (d u v : ℚ))
    (hp : 0 < RamRoundingInit.support I.weight) (htotal : 0 < LargeBallRounding.total I)
    (hdiag : ∀ v,d v v=0)
    (htri : ∀ u v t,(d u t : ℚ) ≤ (d u v : ℚ)+(d v t : ℚ))
    (hsep : 1 ≤ LargeBallRounding.distanceSeparation I (MetricMatrix.rational d))
    (W : ℕ) (hW : (wordBound (baseBound P)).eval (bitSize (encodeInput kind I)) ≤ W) :
    Spec (2^W) (fun σ => RamMetricRounding.Input I d σ ∧
      RamRegionInvariant.Room n (RamRoundingInit.support I.weight) σ ∧ RamRegionCut.Room n σ)
      RamMetricRounding.command (fun _ τ => RamRegionCut.Output I d (RamRoundingInit.support I.weight) τ)
      ((timeBound (baseBound P)).eval (bitSize (encodeInput kind I))) := by
  let L := bitSize (encodeInput kind I)
  let w := (baseBound P).eval L
  have hn : n ≤ L := input_dimension kind I
  obtain ⟨hw,hwg,hcg,hdg,hcost,hprefix⟩ := data_bounds P kind I d hd
  have hW' : RamRoundingBudget.width n w ≤ W := by
    rw [eval_word] at hW
    exact (width_mono hn).trans hW
  have hb := RamRoundingBudget.command_spec W w I d hw hW' hwg hcg hdg hcost hprefix hp htotal hdiag htri hsep
  have htotalHeight : Height (2^w) (RamRoundingInit.total I.weight : ℚ) := by
    simpa only [List.take_length,RamRoundingInit.total] using hprefix (List.ofFn I.weight).length
  have ht := (time_bound n (RamRoundingInit.support I.weight) w (RamRoundingInit.total I.weight)
    (RamRoundingBudget.support_le I) (den_bound htotalHeight)).trans (time_mono hn)
  intro σ hσ
  obtain ⟨τ,rr,pr⟩ := hb σ hσ
  exact ⟨τ,rr.mono (by simpa only [eval_time] using ht),pr⟩

end Lax455465Proofs.RamUniformRounding
