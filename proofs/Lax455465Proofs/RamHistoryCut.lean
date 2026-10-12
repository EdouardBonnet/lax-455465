import Lax455465Proofs.RamHistoryPotential

set_option maxRecDepth 8192
namespace Lax455465Proofs.RamHistoryCut
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar RamRegionContext RamRegionRecord
open Lax455465.RationalEncoding HistoryPotentialData
open scoped BigOperators NNRat

structure Input {n : ℕ} (I : RationalInstance n) (d : MetricMatrix.Matrix n) (history : List (Entry n)) (σ : Env) : Prop where
  nValue : σ.vars "metric.n"=n
  n2Value : σ.vars "metric.n2"=n*n
  historyPosition : σ.vars "history.pos"=4*history.length
  metric : Prefix (RamUnsignedBuffer.encode (MetricMatrix.values d)) "metric.old" σ
  records : Prefix (words history) "region.history" σ
  weights : Prefix (RamUnsignedBuffer.encode (List.ofFn I.weight)) "flow.weights" σ
  capacities : Prefix (RamUnsignedBuffer.encode (MetricMatrix.values I.capacity)) "flow.capacities" σ
  total : Stored "round.total" (RamRoundingInit.total I.weight) σ
  potentialRoom : 2*n < (σ.arrs "cut.potential").length
  maskRoom : 2*n < (σ.arrs "cut.flags").length
  crossingRoom : 2*(n*n) < (σ.arrs "cut.crossing").length

def command : Com := .seq RamHistoryPotential.command RamPotentialSweep.command
def cost (n m M : ℕ) : ℕ := RamHistoryPotential.cost n m+RamPotentialSweep.cost n M

/-- Compute the actual ordering potential and choose its best admissible
upper threshold, retaining the chosen shore in the output mask. -/
theorem command_spec (B M : ℕ) {n : ℕ} (I : RationalInstance n) (d : MetricMatrix.Matrix n) (history : List (Entry n))
    (hM : 1 ≤ M) (hm : 2*history.length ≤ M) (hB : 2*M^2+3 < B) (h4 : 4 < B)
    (hlen : 4*history.length < B) (hindex : 2*(n*n)+2 < B) (hvertex : 2*n+2 < B)
    (hd : ∀ u w,LpInputSize.Height M (d u w : ℚ)) (hr : ∀ e∈history,LpInputSize.Height M (e.radius : ℚ))
    (hcuts : ∀ S,CutScoreHeight.Bounds I S M) (U : ℚ)
    (hgood : ∃ S∈CutSweeps.candidates (ThresholdCutData.potential true (values d history)),
      CutSweeps.admissibleQ I S ∧ CutSweeps.ratioQ I S ≤ U) :
    Spec B (Input I d history) command
      (fun _ τ => ∃ S : Finset (Fin n),CutSweeps.admissibleQ I S ∧ CutSweeps.ratioQ I S ≤ U ∧
        Prefix (RamUnsignedBuffer.encode (CutScoreData.vertexFlags S)) "cut.flags" τ) (cost n history.length M) := by
  obtain ⟨S,hS,hvalid,hratio⟩ := hgood
  obtain ⟨j,hj,hjn,hjvalid,hjratio⟩ := RamPotentialSweep.selected_le I (values d history) true S hS hvalid
  rintro σ hσ
  obtain ⟨ν,rp,pp⟩ := RamHistoryPotential.command_spec B M d history hM hm hB h4 hlen hindex hvertex hd hr σ
    ⟨hσ.nValue,hσ.historyPosition,hσ.metric,hσ.records,hσ.potentialRoom⟩
  have hinput : RamThresholdCandidate.Input I (values d history) true ν := by
    exact ⟨pp.1.1,(rp.frame_var _ (by decide)).trans hσ.n2Value,pp.2.2.1,pp.2.1,
      RamRoundingConstants.storedFrame rp hσ.total (by decide) (by decide),
      by simpa only [Prefix,rp.frame_arr "flow.weights" (by decide)] using hσ.weights,
      by simpa only [Prefix,rp.frame_arr "flow.capacities" (by decide)] using hσ.capacities,
      pp.2.2.2,
      by rw [RamFrames.run_array_length rp]; exact hσ.maskRoom,
      by rw [RamFrames.run_array_length rp]; exact hσ.crossingRoom⟩
  obtain ⟨τ,rs,ps⟩ := RamPotentialSweep.command_spec B M I (values d history) true hM hB hindex hvertex
    (value_height d history M hM hm) (fun i hi => hcuts _) ν hinput
  have hmask : Prefix (RamUnsignedBuffer.encode (CutScoreData.vertexFlags (ThresholdCutData.candidate true (values d history) j))) "cut.flags" τ := by
    simpa only [hj,RamPotentialSweep.Selected] using ps.2.2
  exact ⟨τ,rp.seq rs,ThresholdCutData.candidate true (values d history) j,hjvalid,hjratio.trans hratio,hmask⟩

/-- A completed valid small-region history supplies the quantitative cut
bound to the native algorithm; it is not an extra certificate in the input. -/
theorem history_spec (B M : ℕ) {n : ℕ} (I : RationalInstance n) (d : MetricMatrix.Matrix n) (history : List (Entry n))
    (p : ℕ) (hM : 1 ≤ M) (hm : 2*history.length ≤ M) (hB : 2*M^2+3 < B) (h4 : 4 < B)
    (hlen : 4*history.length < B) (hindex : 2*(n*n)+2 < B) (hvertex : 2*n+2 < B)
    (hd : ∀ u w,LpInputSize.Height M (d u w : ℚ)) (hr : ∀ e∈history,LpInputSize.Height M (e.radius : ℚ))
    (hcuts : ∀ S,CutScoreHeight.Bounds I S M) (htotal : 0 < LargeBallRounding.total I)
    (hp : 0 < p) (hcount : history.length ≤ p)
    (hvalid : RegionLoop.ValidHistory I (MetricMatrix.rational d)
      (RegionRounding.metricCost I (MetricMatrix.rational d)/p) (RegionRounding.radiusBudget I) p Finset.univ
      (history.map Entry.region)) :
    Spec B (Input I d history) command
      (fun _ τ => ∃ S : Finset (Fin n),CutSweeps.admissibleQ I S ∧
        CutSweeps.ratioQ I S ≤ (288/5 : ℚ)*(RegionBudget.steps p : ℚ)*RegionRounding.metricCost I (MetricMatrix.rational d) ∧
        Prefix (RamUnsignedBuffer.encode (CutScoreData.vertexFlags S)) "cut.flags" τ) (cost n history.length M) := by
  let history' := history.map Entry.region
  let W := RegionRounding.metricCost I (MetricMatrix.rational d)
  have hdelta : 0 < RegionRounding.radiusBudget I := by unfold RegionRounding.radiusBudget; positivity
  have hW : 0 ≤ W := RegionCharging.weight_nonnegative _ _ (fun _ _ => NNRat.coe_nonneg _) (fun _ _ => NNRat.coe_nonneg _)
  have hc := HistoryCharging.total_charge I (MetricMatrix.rational d) (RegionRounding.radiusBudget I) p history' hp
    (by simpa only [history',List.length_map] using hcount) hdelta (fun _ _ => NNRat.coe_nonneg _) hvalid
  have heq : 2*RegionSearch.slope (RegionBudget.steps p) (RegionRounding.radiusBudget I)*W =
      8*(RegionBudget.steps p : ℚ)*BalancedRegionCut.total I^2*W := by
    unfold RegionSearch.slope RegionRounding.radiusBudget
    change 2*((RegionBudget.steps p : ℚ)/(1/(4*LargeBallRounding.total I^2)))*W =
      8*(RegionBudget.steps p : ℚ)*LargeBallRounding.total I^2*W
    field_simp [ne_of_gt htotal]
    ring
  change (∑ j : Fin history'.length,RegionOrdering.chargedBoundary (fun u v => (I.capacity u v : ℚ))
    (RegionHistory.index (MetricMatrix.rational d) history') (RegionHistory.orientation history') j) ≤
      2*RegionSearch.slope (RegionBudget.steps p) (RegionRounding.radiusBudget I)*W at hc
  rw [heq] at hc
  obtain ⟨S,hS,hadm,hbound⟩ := BalancedRegionCut.round_ratio I (RegionHistory.index (MetricMatrix.rational d) history')
    (RegionHistory.orientation history') (RegionBudget.steps p) W htotal (Nat.cast_nonneg _) hW
    (RegionHistory.blocks_small I (MetricMatrix.rational d) _ _ _ history' hvalid htotal) hc
  exact command_spec B M I d history hM hm hB h4 hlen hindex hvertex hd hr hcuts _
    ⟨S,HistoryPotentialData.round_mem I d history S hS hadm,hadm,hbound⟩

end Lax455465Proofs.RamHistoryCut
