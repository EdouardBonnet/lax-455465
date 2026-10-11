import Lax455465Proofs.MetricCostHeight
import Lax455465Proofs.RamUnsignedScalar

namespace Lax455465Proofs.RamMetricCost

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamVirtualState RamUnsignedScalar
open Lax455465.RationalEncoding Lax759944.BinaryWordEncoding MetricMatrix LpInputSize
open scoped NNRat

def command : Com := .seq (.assign "sum.count" (.var "metric.n2"))
  (.seq (RamProductSum.command "flow.capacities" "metric.old") (save "round.cost"))

/-- The actual native metric cost equals the cost in the rounding theorem.
All accumulator heights follow from the source capacities and metric heights. -/
theorem command_spec (B : ℕ) {n : ℕ} (kind : Lax455465.ProductNetwork.EdgeKind)
    (I : RationalInstance n) (d : Matrix n) (K : ℕ) (hd : ∀ u v, Height (2^K) (d u v : ℚ))
    (hB : 2*(2^(MetricCostHeight.exponent n (bitSize (encodeInput kind I)) K))^2+3 < B)
    (hindex : 2*(n*n)+2 < B) :
    Spec B (fun σ => σ.vars "metric.n2" = n*n ∧
      Prefix (RamUnsignedBuffer.encode (values I.capacity)) "flow.capacities" σ ∧
      Prefix (RamUnsignedBuffer.encode (values d)) "metric.old" σ) command
      (fun _ τ => Stored "round.cost" (MetricCostData.cost I d) τ)
      ((144*MetricCostHeight.exponent n (bitSize (encodeInput kind I)) K+296)*(n*n)+22) := by
  let L := bitSize (encodeInput kind I)
  let V := MetricCostHeight.exponent n L K
  let M := 2^V
  let xs := values I.capacity
  let ys := values d
  let qs := RamProductSum.products xs ys
  have hxlen : xs.length = n*n := length_values _
  have hylen : ys.length = n*n := length_values _
  have hqlen : qs.length = n*n := by simp only [qs,RamProductSum.products,List.length_ofFn,xs,length_values]
  have hdom : L+K ≤ V := by
    have hh : L+K ≤ (L+K)*(n*n+1) := Nat.le_mul_of_pos_right _ (by omega)
    dsimp only [V,MetricCostHeight.exponent]
    omega
  have hL : 2^L ≤ M := Nat.pow_le_pow_right (by decide) (by omega)
  have hK : 2^K ≤ M := Nat.pow_le_pow_right (by decide) (by omega)
  have hLK : 2^(L+K) ≤ M := Nat.pow_le_pow_right (by decide) hdom
  have hM : M < B := by dsimp only [M,V,L]; nlinarith
  have hxn : ∀ q ∈ xs, q.num ≤ M := by
    intro q hq
    obtain ⟨e,rfl⟩ := List.mem_ofFn.mp hq
    have hh := height_mono (capacity_height kind I ((DirectedFlowLP.edgeIndex n).symm e).1 ((DirectedFlowLP.edgeIndex n).symm e).2) hL
    simpa only [NNRat.natAbs_num_coe] using hh.1
  have hxd : ∀ q ∈ xs, q.den ≤ M := by
    intro q hq
    obtain ⟨e,rfl⟩ := List.mem_ofFn.mp hq
    have hh := height_mono (capacity_height kind I ((DirectedFlowLP.edgeIndex n).symm e).1 ((DirectedFlowLP.edgeIndex n).symm e).2) hL
    simpa only [NNRat.den_coe] using hh.2
  have hyn : ∀ q ∈ ys, q.num ≤ M := by
    intro q hq
    obtain ⟨e,rfl⟩ := List.mem_ofFn.mp hq
    have hh := height_mono (hd ((DirectedFlowLP.edgeIndex n).symm e).1 ((DirectedFlowLP.edgeIndex n).symm e).2) hK
    simpa only [NNRat.natAbs_num_coe] using hh.1
  have hyd : ∀ q ∈ ys, q.den ≤ M := by
    intro q hq
    obtain ⟨e,rfl⟩ := List.mem_ofFn.mp hq
    have hh := height_mono (hd ((DirectedFlowLP.edgeIndex n).symm e).1 ((DirectedFlowLP.edgeIndex n).symm e).2) hK
    simpa only [NNRat.den_coe] using hh.2
  have hph := MetricCostHeight.products_height kind I d K hd
  have hpn : ∀ q ∈ qs, q.num ≤ M := by
    intro q hq
    simpa only [NNRat.natAbs_num_coe] using (height_mono (hph q hq) hLK).1
  have hpd : ∀ q ∈ qs, q.den ≤ M := by
    intro q hq
    simpa only [NNRat.den_coe] using (height_mono (hph q hq) hLK).2
  have hprefix := MetricCostHeight.prefix_height kind I d K hd
  have hpreN : ∀ i, (qs.take i).sum.num ≤ M := by
    intro i
    simpa only [NNRat.natAbs_num_coe] using (hprefix i).1
  have hpreD : ∀ i, (qs.take i).sum.den ≤ M := by
    intro i
    simpa only [NNRat.den_coe] using (hprefix i).2
  have hfinal : (MetricCostData.cost I d).num ≤ M ∧ (MetricCostData.cost I d).den ≤ M := by
    simpa only [MetricCostData.cost,List.take_length] using And.intro (hpreN qs.length) (hpreD qs.length)
  rintro σ ⟨hn2,hxp,hyp⟩
  let ν := σ.setVar "sum.count" (n*n)
  have rcount : Run B (.assign "sum.count" (.var "metric.n2")) σ ν 2 :=
    Run.assign (by rw [evalB_var_iff]; exact ⟨hn2.symm,hn2 ▸ (by omega : n*n < B)⟩)
  have hctx : RamProductSum.Context "flow.capacities" "metric.old" xs ys ν := by
    refine ⟨by simp [ν,hxlen],?_,?_⟩
    · simpa only [ν,Prefix,arrs_setVar,xs] using hxp
    · simpa only [ν,Prefix,arrs_setVar,ys] using hyp
  obtain ⟨μ,rsum,psum⟩ := RamProductSum.command_spec B M "flow.capacities" "metric.old" xs ys
    (by omega) hB (by rwa [hxlen]) hxn hxd hyn hyd hpn hpd hpreN hpreD ν hctx
  obtain ⟨τ,rsave,psave⟩ := save_spec B "round.cost" (MetricCostData.cost I d)
    (hfinal.1.trans_lt hM) (hfinal.2.trans_lt hM) (by decide) μ psum.2
  have hsize : (M^2).size = 2*V+1 := by
    dsimp only [M]
    rw [←Nat.pow_mul,Nat.size_pow]
    omega
  refine ⟨τ,(rcount.seq (rsum.seq rsave)).mono ?_,psave⟩
  rw [hxlen,hsize]
  dsimp only [V,L]
  ring_nf
  omega

end Lax455465Proofs.RamMetricCost
