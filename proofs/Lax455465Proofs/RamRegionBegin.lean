import Lax455465Proofs.RamRegionBoundedLoop
import Lax455465Proofs.RamRoundingInit

namespace Lax455465Proofs.RamRegionBegin
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar RamRegionInvariant
open Lax455465.RationalEncoding
open scoped NNRat

structure Source {n : ℕ} (I : RationalInstance n) (length : MetricMatrix.Matrix n)
    (seed beta delta : ℚ≥0) (p : ℕ) (σ : Env) : Prop where
  nValue : σ.vars "metric.n"=n
  n2Value : σ.vars "metric.n2"=n*n
  supportValue : σ.vars "round.support"=p
  stepsValue : σ.vars "round.steps"=RegionBudget.steps p
  seedData : Stored "round.seed" seed σ
  betaData : Stored "round.slope" beta σ
  deltaData : Stored "round.delta" delta σ
  unitData : Stored "round.gridStep" (delta/(RegionBudget.steps p : ℚ≥0)) σ
  totalData : Stored "round.total" (RamRoundingInit.total I.weight) σ
  weightsData : Prefix (RamUnsignedBuffer.encode (List.ofFn I.weight)) "flow.weights" σ
  capacityData : Prefix (RamUnsignedBuffer.encode (MetricMatrix.values I.capacity)) "flow.capacities" σ
  lengthData : Prefix (RamUnsignedBuffer.encode (MetricMatrix.values length)) "metric.old" σ

def setup : Com := .seq (.assign "history.pos" (.lit 0))
  (.seq (.assign "region.phase" (.lit 0)) (.assign "loop.limit" (.add (.var "round.support") (.lit 1))))
def command : Com := .seq RamLargeThreshold.command (.seq RamActiveInit.command setup)

def sourceNames : List String := ["metric.n","metric.n2","round.support","round.steps",
  "round.seed.n","round.seed.d","round.slope.n","round.slope.d","round.delta.n","round.delta.d",
  "round.gridStep.n","round.gridStep.d","round.total.n","round.total.d"]

theorem Source.frame {B K : ℕ} {cmd : Com} {σ τ : Env} (rr : Run B cmd σ τ K)
    {n : ℕ} {I : RationalInstance n} {length : MetricMatrix.Matrix n} {seed beta delta : ℚ≥0} {p : ℕ}
    (h : Source I length seed beta delta p σ)
    (hx : ∀ x∈sourceNames, x∉cmd.wvars) (ha : ∀ a∈RamRegionInvariant.arrays, a∉cmd.warrs) :
    Source I length seed beta delta p τ := by
  exact ⟨(rr.frame_var _ (hx _ (by simp [sourceNames]))).trans h.nValue,
    (rr.frame_var _ (hx _ (by simp [sourceNames]))).trans h.n2Value,
    (rr.frame_var _ (hx _ (by simp [sourceNames]))).trans h.supportValue,
    (rr.frame_var _ (hx _ (by simp [sourceNames]))).trans h.stepsValue,
    RamRoundingConstants.storedFrame rr h.seedData (hx _ (by simp [sourceNames])) (hx _ (by simp [sourceNames])),
    RamRoundingConstants.storedFrame rr h.betaData (hx _ (by simp [sourceNames])) (hx _ (by simp [sourceNames])),
    RamRoundingConstants.storedFrame rr h.deltaData (hx _ (by simp [sourceNames])) (hx _ (by simp [sourceNames])),
    RamRoundingConstants.storedFrame rr h.unitData (hx _ (by simp [sourceNames])) (hx _ (by simp [sourceNames])),
    RamRoundingConstants.storedFrame rr h.totalData (hx _ (by simp [sourceNames])) (hx _ (by simp [sourceNames])),
    by simpa only [Prefix,rr.frame_arr "flow.weights" (ha _ (by simp [RamRegionInvariant.arrays]))] using h.weightsData,
    by simpa only [Prefix,rr.frame_arr "flow.capacities" (ha _ (by simp [RamRegionInvariant.arrays]))] using h.capacityData,
    by simpa only [Prefix,rr.frame_arr "metric.old" (ha _ (by simp [RamRegionInvariant.arrays]))] using h.lengthData⟩

set_option maxHeartbeats 2400000 in
/-- Initialize the physical loop from the previously computed total and
constants: compute the large threshold, activate all vertices, and clear
only the initialized history length and loop control registers. -/
theorem command_spec (B M : ℕ) {n : ℕ} (I : RationalInstance n) (length : MetricMatrix.Matrix n)
    (seed beta delta : ℚ≥0) (p : ℕ) (hM : 3≤M) (hB : 2*M^2+3<B)
    (ht : LpInputSize.Height M (RamRoundingInit.total I.weight : ℚ)) (hindex : 2*n+2<B) (hcount : p+1<B) :
    Spec B (fun σ => Source I length seed beta delta p σ ∧ Room n p σ) command
      (fun _ τ => Fixed I length seed beta delta (RamLargeThreshold.threshold (RamRoundingInit.total I.weight)) p τ ∧
        Room n p τ ∧ τ.vars "loop.limit"=p+1 ∧ RamRegionState.View I length seed beta (RamRegionBoundedLoop.initial n) τ)
      (36*((RamRoundingInit.total I.weight).den*3).size+28*n+112) := by
  have h2 : 2<B := by nlinarith
  rintro σ ⟨hσ,hroom⟩
  obtain ⟨σ1,r1,p1⟩ := RamLargeThreshold.command_spec B M (RamRoundingInit.total I.weight) hM hB ht σ hσ.totalData
  have hs1 := Source.frame r1 hσ (by dsimp [sourceNames]; decide) (by dsimp [RamRegionInvariant.arrays]; decide)
  have room1 := Room.frame r1 hroom
  have hf1 : Fixed I length seed beta delta (RamLargeThreshold.threshold (RamRoundingInit.total I.weight)) p σ1 :=
    ⟨hs1.nValue,hs1.n2Value,hs1.supportValue,hs1.stepsValue,hs1.seedData,hs1.betaData,hs1.deltaData,hs1.unitData,
      p1.2,hs1.weightsData,hs1.capacityData,hs1.lengthData⟩
  obtain ⟨σ2,r2,p2⟩ := RamActiveInit.command_spec B n h2 hindex σ1
    ⟨hf1.nValue,room1 "region.active" (2*n) (by simp [extents])⟩
  have hf2 := Fixed.frame r2 hf1 (by dsimp [names]; decide) (by dsimp [RamRegionInvariant.arrays]; decide)
  have room2 := Room.frame r2 room1
  let σ3 := σ2.setVar "history.pos" 0
  let σ4 := σ3.setVar "region.phase" 0
  let τ := σ4.setVar "loop.limit" (p+1)
  have r3 : Run B (.assign "history.pos" (.lit 0)) σ2 σ3 2 := Run.assign (evalB_lit (by omega))
  have r4 : Run B (.assign "region.phase" (.lit 0)) σ3 σ4 2 := Run.assign (evalB_lit (by omega))
  have hsupp : σ4.vars "round.support"=p := ((r3.seq r4).frame_var _ (by decide)).trans hf2.supportValue
  have r5 : Run B (.assign "loop.limit" (.add (.var "round.support") (.lit 1))) σ4 τ 4 :=
    Run.assign (evalB_bin (op := .add) (by rw [evalB_var_iff]; exact ⟨hsupp.symm,hsupp ▸ (by omega : p<B)⟩)
      (evalB_lit (by omega)) hcount)
  have rsetup := r3.seq (r4.seq r5)
  have rr := r1.seq (r2.seq rsetup)
  refine ⟨τ,rr.mono (by omega),Fixed.frame rsetup hf2 (by dsimp [names]; decide)
    (by dsimp [RamRegionInvariant.arrays]; decide),Room.frame rsetup room2,by simp [τ],?_⟩
  change RamRegionInvariant.Dynamic Finset.univ [] τ
  refine ⟨by simp [τ,σ4],?_,?_,by simp [τ,σ4,σ3]⟩
  · have hm : ResidualData.mask (Finset.univ : Finset (Fin n))=(fun _ : Fin n => true) := by funext v; simp [ResidualData.mask]
    simpa only [hm,Prefix,rsetup.frame_arr "region.active" (by decide)] using p2.2
  · simp [RamRegionRecord.words,Prefix]

end Lax455465Proofs.RamRegionBegin
