import Lax455465Proofs.RamRoundingDispatch

set_option maxRecDepth 8192
namespace Lax455465Proofs.RamMetricRounding
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamUnsignedScalar RamRegionInvariant RamRegionContext RamVirtualState
open Lax455465.RationalEncoding
open scoped NNRat BigOperators

structure Input {n : ℕ} (I : RationalInstance n) (length : MetricMatrix.Matrix n) (σ : Env) : Prop where
  nValue : σ.vars "metric.n"=n
  n2Value : σ.vars "metric.n2"=n*n
  weights : Prefix (RamUnsignedBuffer.encode (List.ofFn I.weight)) "flow.weights" σ
  capacities : Prefix (RamUnsignedBuffer.encode (MetricMatrix.values I.capacity)) "flow.capacities" σ
  distances : Prefix (RamUnsignedBuffer.encode (MetricMatrix.values length)) "metric.old" σ
  costData : Stored "round.cost" (MetricCostData.cost I length) σ

def command : Com := .seq RamRoundingInit.command RamRoundingDispatch.command

set_option maxHeartbeats 6400000 in
/-- Initialize all growth constants from the original weight vector and
metric cost, then construct a cut through the appropriate native branch. -/
theorem command_spec (B M H N : ℕ) {n : ℕ} (I : RationalInstance n) (length : MetricMatrix.Matrix n)
    (seed beta delta : ℚ≥0) (p : ℕ)
    (hM : 4≤M) (hk : RegionBudget.steps p≤M) (hB : 2*M^2+3<B) (hquery : 2*(2^H)^2+3<B)
    (hindex : 2*(n*n)+2<B) (hvertex : 2*n+4<B) (hradius : 2*(RegionBudget.steps p+1+2*n)+2<B)
    (hlen : 4*p+4<B) (hthreshold : LpInputSize.Height (2^H) (RamLargeThreshold.threshold (RamRoundingInit.total I.weight) : ℚ))
    (hwn : ∀ v, (I.weight v).num≤M) (hwd : ∀ v, (I.weight v).den≤M)
    (hcn : ∀ u v, (I.capacity u v).num≤M) (hcd : ∀ u v, (I.capacity u v).den≤M)
    (hl : ∀ u v, LpInputSize.Height M (length u v : ℚ))
    (hd : LpInputSize.Height M (delta : ℚ))
    (hu : LpInputSize.Height M ((delta/(RegionBudget.steps p : ℚ≥0) : ℚ≥0) : ℚ))
    (hb : ∀ active : Finset (Fin n), ∀ root : Fin n, ∀ i,
      ∀ hi : i<(RadiusData.candidates (length root) (fun v => length v root) (RegionBudget.steps p) delta).length,
      RegionQueryHeight.Bounds (RadiusSearchData.atRadius (RegionExecutionData.query I length active root seed beta)
        (RadiusData.candidates (length root) (fun v => length v root) (RegionBudget.steps p) delta)[i]) H)
    (hbeta : (beta : ℚ)=RegionSearch.slope (RegionBudget.steps p) delta)
     (hdelta : 0<(delta : ℚ)) (hp : 0<p)
    (hdiag : ∀ v, length v v=0)
    (htri : ∀ u v w, (length u w : ℚ)≤(length u v : ℚ)+(length v w : ℚ))
    (hcost : RegionRounding.metricCost I (MetricMatrix.rational length)≤(p : ℚ)*(seed : ℚ))
    (hsupport : (RegionSelection.support (RegionLoop.weights I Finset.univ)).card≤p)
    (htotal : LpInputSize.Height M (RamRoundingInit.total I.weight : ℚ))
    (hN : 1 ≤ N) (hMN : M*M ≤ N) (hpN : 2*p ≤ N) (hNB : 2*N^2+3 < B)
    (hlargeBounds : ∀ Tin Tout : Finset (Fin n),∀ hin : Tin.Nonempty,∀ hout : Tout.Nonempty,
      LargePotentialData.Bounds I length Tin Tout hin hout N)
    (hcuts : ∀ S,CutScoreHeight.Bounds I S N)
    (htotalPos : 0 < LargeBallRounding.total I)
    (hsep : 1 ≤ LargeBallRounding.distanceSeparation I (MetricMatrix.rational length))
    (hseedEq : (seed : ℚ)=RegionRounding.metricCost I (MetricMatrix.rational length)/p)
    (hdeltaEq : (delta : ℚ)=RegionRounding.radiusBudget I)
    (hpEq : p=RamRoundingInit.support I.weight)
    (hconstants : RoundingConstantHeight.Bounds (MetricCostData.cost I length) (RamRoundingInit.total I.weight) p M)
    (hprefix : ∀ i,LpInputSize.Height M (((List.ofFn I.weight).take i).sum : ℚ)) :
    Spec B (fun σ => Input I length σ ∧ Room n p σ ∧ RamRegionCut.Room n σ)
      command (fun _ τ => RamRegionCut.Output I length p τ)
      (((36*(M^2).size+200)*(n+1)+600*(M^2).size+2000)+
        (36*((RamRoundingInit.total I.weight).den*3).size+28*n+116+
          RamRegionBoundedLoop.cost n p M H+RamRegionCut.cost n p N+RamZeroCut.cost n N)) := by
  have htotalCoe : (RamRoundingInit.total I.weight : ℚ)=LargeBallRounding.total I := by
    simp [RamRoundingInit.total,LargeBallRounding.total,List.sum_ofFn,NNRat.cast_sum]
  have hseedVal : RoundingConstants.seed (MetricCostData.cost I length) p=seed := by
    apply NNRat.coe_injective
    simp only [RoundingConstants.seed,NNRat.coe_div,NNRat.coe_natCast,MetricCostData.coe_cost,hseedEq]
  have hdeltaVal : RoundingConstants.delta (RamRoundingInit.total I.weight)=delta := by
    apply NNRat.coe_injective
    rw [RoundingConstants.coe_delta,htotalCoe,hdeltaEq]
    rfl
  have hbetaVal : RoundingConstants.beta (RamRoundingInit.total I.weight) p=beta := by
    apply NNRat.coe_injective
    rw [RoundingConstants.coe_beta,hdeltaVal,hbeta]
  have hw : ∀ v,LpInputSize.Height M (I.weight v : ℚ) := by
    intro v
    exact ⟨by simpa only [NNRat.natAbs_num_coe] using hwn v,by simpa only [NNRat.den_coe] using hwd v⟩
  rintro σ ⟨hσ,hregionRoom,hcutRoom⟩
  obtain ⟨ν,rr,hin,hconst,hseedν,hdeltaν,hbetaν,hunitν⟩ := RamRoundingInit.command_spec B M I.weight
    (MetricCostData.cost I length) (by simpa only [←hpEq] using hconstants) hM hB hvertex
    (by simpa only [←hpEq] using hp) hw hprefix σ ⟨hσ.nValue,hσ.weights,hσ.costData⟩
  have hsource : RamRegionBegin.Source I length seed beta delta p ν := by
    exact ⟨hin.nValue,(rr.frame_var _ (by decide)).trans hσ.n2Value,
      by simpa only [←hpEq] using hconst.supportValue,
      by simpa only [←hpEq] using hconst.stepsValue,
      by simpa only [←hpEq,hseedVal] using hseedν,
      by simpa only [←hpEq,hbetaVal] using hbetaν,
      by simpa only [hdeltaVal] using hdeltaν,
      by simpa only [←hpEq,RoundingConstants.gridStep,hdeltaVal] using hunitν,
      hconst.totalData,hin.weightsData,
      by simpa only [Prefix,rr.frame_arr "flow.capacities" (by decide)] using hσ.capacities,
      by simpa only [Prefix,rr.frame_arr "metric.old" (by decide)] using hσ.distances⟩
  have hMN' : M ≤ N := by nlinarith
  obtain ⟨τ,rd,pd⟩ := RamRoundingDispatch.command_spec B M H N I length seed beta delta p (by omega) hk hB hquery hindex (by omega)
    hradius hlen hthreshold hwn hwd hcn hcd hl hd hu hb hbeta hdelta hp hdiag htri hcost hsupport htotal
    hN hMN hpN hNB hlargeBounds hcuts htotalPos hsep hseedEq hdeltaEq
    (LpInputSize.height_mono hconstants.costBound hMN') ν ⟨hsource,hregionRoom.frame rr,hcutRoom.frame rr,hin.costData⟩
  exact ⟨τ,rr.seq rd,pd⟩

end Lax455465Proofs.RamMetricRounding
