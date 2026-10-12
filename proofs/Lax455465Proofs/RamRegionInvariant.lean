import Lax455465Proofs.RamRegionIteration
import Lax455465Proofs.RamResidual

namespace Lax455465Proofs.RamRegionInvariant
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar
open Lax455465.RationalEncoding RamRegionRecord
open scoped NNRat

structure Fixed {n : ℕ} (I : RationalInstance n) (length : MetricMatrix.Matrix n)
    (seed beta delta threshold : ℚ≥0) (p : ℕ) (σ : Env) : Prop where
  nValue : σ.vars "metric.n"=n
  n2Value : σ.vars "metric.n2"=n*n
  supportValue : σ.vars "round.support"=p
  stepsValue : σ.vars "round.steps"=RegionBudget.steps p
  seedData : Stored "round.seed" seed σ
  betaData : Stored "round.slope" beta σ
  deltaData : Stored "round.delta" delta σ
  unitData : Stored "round.gridStep" (delta/(RegionBudget.steps p : ℚ≥0)) σ
  thresholdData : Stored "round.largeThreshold" threshold σ
  weightsData : Prefix (RamUnsignedBuffer.encode (List.ofFn I.weight)) "flow.weights" σ
  capacityData : Prefix (RamUnsignedBuffer.encode (MetricMatrix.values I.capacity)) "flow.capacities" σ
  lengthData : Prefix (RamUnsignedBuffer.encode (MetricMatrix.values length)) "metric.old" σ

def names : List String := ["metric.n","metric.n2","round.support","round.steps",
  "round.seed.n","round.seed.d","round.slope.n","round.slope.d",
  "round.delta.n","round.delta.d","round.gridStep.n","round.gridStep.d",
  "round.largeThreshold.n","round.largeThreshold.d"]
def arrays : List String := ["flow.weights","flow.capacities","metric.old"]

theorem Fixed.frame {B K : ℕ} {cmd : Com} {σ τ : Env} (rr : Run B cmd σ τ K)
    {n : ℕ} {I : RationalInstance n} {length : MetricMatrix.Matrix n} {seed beta delta threshold : ℚ≥0} {p : ℕ}
    (h : Fixed I length seed beta delta threshold p σ)
    (hx : ∀ x∈names, x∉cmd.wvars) (ha : ∀ a∈arrays, a∉cmd.warrs) :
    Fixed I length seed beta delta threshold p τ := by
  exact ⟨(rr.frame_var _ (hx _ (by simp [names]))).trans h.nValue,
    (rr.frame_var _ (hx _ (by simp [names]))).trans h.n2Value,
    (rr.frame_var _ (hx _ (by simp [names]))).trans h.supportValue,
    (rr.frame_var _ (hx _ (by simp [names]))).trans h.stepsValue,
    RamRoundingConstants.storedFrame rr h.seedData (hx _ (by simp [names])) (hx _ (by simp [names])),
    RamRoundingConstants.storedFrame rr h.betaData (hx _ (by simp [names])) (hx _ (by simp [names])),
    RamRoundingConstants.storedFrame rr h.deltaData (hx _ (by simp [names])) (hx _ (by simp [names])),
    RamRoundingConstants.storedFrame rr h.unitData (hx _ (by simp [names])) (hx _ (by simp [names])),
    RamRoundingConstants.storedFrame rr h.thresholdData (hx _ (by simp [names])) (hx _ (by simp [names])),
    by simpa only [Prefix,rr.frame_arr "flow.weights" (ha _ (by simp [arrays]))] using h.weightsData,
    by simpa only [Prefix,rr.frame_arr "flow.capacities" (ha _ (by simp [arrays]))] using h.capacityData,
    by simpa only [Prefix,rr.frame_arr "metric.old" (ha _ (by simp [arrays]))] using h.lengthData⟩

structure Dynamic {n : ℕ} (active : Finset (Fin n)) (history : List (Entry n)) (σ : Env) : Prop where
  phase : σ.vars "region.phase"=0
  activeData : Prefix (RamUnsignedBuffer.encode (MaskedMassData.flags (ResidualData.mask active))) "region.active" σ
  historyData : Prefix (words history) "region.history" σ
  historyPosition : σ.vars "history.pos"=4*history.length

def dynamicNames : List String := ["region.phase","history.pos"]
def dynamicArrays : List String := ["region.active","region.history"]

theorem Dynamic.frame {B K : ℕ} {cmd : Com} {σ τ : Env} (rr : Run B cmd σ τ K)
    {n : ℕ} {active : Finset (Fin n)} {history : List (Entry n)} (h : Dynamic active history σ)
    (hx : ∀ x∈dynamicNames, x∉cmd.wvars) (ha : ∀ a∈dynamicArrays, a∉cmd.warrs) : Dynamic active history τ := by
  exact ⟨(rr.frame_var _ (hx _ (by simp [dynamicNames]))).trans h.phase,
    by simpa only [Prefix,rr.frame_arr "region.active" (ha _ (by simp [dynamicArrays]))] using h.activeData,
    by simpa only [Prefix,rr.frame_arr "region.history" (ha _ (by simp [dynamicArrays]))] using h.historyData,
    (rr.frame_var _ (hx _ (by simp [dynamicNames]))).trans h.historyPosition⟩

def extents (n p : ℕ) : List (String×ℕ) := [
  ("region.arcActive",2*n*n),("region.capacities",2*n*n),("region.weights",2*n),
  ("region.out",2*n),("region.in",2*n),("region.radii",2*(RegionBudget.steps p+1+2*n)),
  ("region.outMask",2*n),("region.inMask",2*n),("region.crossing",2*n*n),
  ("region.active",2*n),("region.nextActive",2*n),("region.history",4*p+4)]

def Room (n p : ℕ) (σ : Env) : Prop := ∀ a count, (a,count)∈extents n p → count<(σ.arrs a).length

theorem Room.frame {B K : ℕ} {cmd : Com} {σ τ : Env} (rr : Run B cmd σ τ K)
    {n p : ℕ} (h : Room n p σ) : Room n p τ := by
  intro a count hm
  rw [RamFrames.run_array_length rr a]
  exact h a count hm

end Lax455465Proofs.RamRegionInvariant
