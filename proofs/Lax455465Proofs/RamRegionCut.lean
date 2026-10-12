import Lax455465Proofs.RamLargeCut
import Lax455465Proofs.RamHistoryCut

set_option maxRecDepth 8192
namespace Lax455465Proofs.RamRegionCut
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar RamRegionRecord RamRegionContext
open Lax455465.RationalEncoding RegionRuntimeState
open scoped BigOperators NNRat

structure Room (n : ℕ) (σ : Env) : Prop where
  potential : RamLargePotential.Room n σ
  mask : 2*n < (σ.arrs "cut.flags").length
  crossing : 2*(n*n) < (σ.arrs "cut.crossing").length

theorem Room.frame {B K : ℕ} {cmd : Com} {σ τ : Env} (rr : Run B cmd σ τ K) {n : ℕ} (h : Room n σ) : Room n τ :=
  ⟨h.potential.frame rr,by rw [RamFrames.run_array_length rr]; exact h.mask,
    by rw [RamFrames.run_array_length rr]; exact h.crossing⟩

def command : Com := .ite (.eq (.var "region.phase") (.lit 1)) RamLargeCut.command RamHistoryCut.command
def cost (n p M : ℕ) : ℕ := RamLargeCut.cost n M+RamHistoryCut.cost n p M+4

def Output {n : ℕ} (I : RationalInstance n) (d : MetricMatrix.Matrix n) (p : ℕ) (σ : Env) : Prop :=
  ∃ S : Finset (Fin n),CutSweeps.admissibleQ I S ∧
    CutSweeps.ratioQ I S ≤ (288/5 : ℚ)*(RegionBudget.steps p : ℚ)*RegionRounding.metricCost I (MetricMatrix.rational d) ∧
    Prefix (RamUnsignedBuffer.encode (CutScoreData.vertexFlags S)) "cut.flags" σ

set_option maxHeartbeats 4800000 in
/-- Dispatch on the actual terminal phase of the region loop. Both
successful cases produce a cut with the same logarithmic-budget bound. -/
theorem command_spec (B M : ℕ) {n : ℕ} (I : RationalInstance n) (d : MetricMatrix.Matrix n)
    (seed beta delta threshold : ℚ≥0) (p : ℕ) (s : State n)
    (hM : 1 ≤ M) (hm : 2*p ≤ M) (hB : 2*M^2+3 < B) (h4 : 4 < B)
    (hlen : 4*p+4 < B) (hindex : 2*(n*n)+2 < B) (hvertex : 2*n+2 < B)
    (hd : ∀ u w,LpInputSize.Height M (d u w : ℚ))
    (hr : ∀ e∈s.history,LpInputSize.Height M (e.radius : ℚ))
    (hlargeBounds : ∀ Tin Tout : Finset (Fin n),∀ hin : Tin.Nonempty,∀ hout : Tout.Nonempty,
      LargePotentialData.Bounds I d Tin Tout hin hout M)
    (hcuts : ∀ S,CutScoreHeight.Bounds I S M) (htotal : 0 < LargeBallRounding.total I)
    (hp : 0 < p) (hdiag : ∀ v,d v v=0)
    (hsep : 1 ≤ LargeBallRounding.distanceSeparation I (MetricMatrix.rational d))
    (htri : ∀ u v w,(d u w : ℚ) ≤ (d u v : ℚ)+(d v w : ℚ))
    (hseed : (seed : ℚ)=RegionRounding.metricCost I (MetricMatrix.rational d)/p)
    (hdelta : (delta : ℚ)=RegionRounding.radiusBudget I)
    (hvalid : RegionRuntimeCorrespondence.ValidFinal I d seed delta p s) :
    Spec B (fun σ => RamRegionInvariant.Fixed I d seed beta delta threshold p σ ∧
      RamRegionState.View I d seed beta s σ ∧ Stored "round.total" (RamRoundingInit.total I.weight) σ ∧ Room n σ)
      command (fun _ τ => Output I d p τ) (cost n p M) := by
  rintro σ ⟨hσ,hview,htσ,hroom⟩
  cases hs : s.status with
  | running => simp only [RegionRuntimeCorrespondence.ValidFinal,hs] at hvalid
  | failed => simp only [RegionRuntimeCorrespondence.ValidFinal,hs] at hvalid
  | exhausted =>
    have hv : RegionLoop.ValidHistory I (MetricMatrix.rational d) seed delta p Finset.univ (s.history.map Entry.region) ∧ s.history.length ≤ p := by
      simpa only [RegionRuntimeCorrespondence.ValidFinal,hs] using hvalid
    have hvw : σ.vars "region.phase"=2 ∧ Prefix (words s.history) "region.history" σ ∧
      σ.vars "history.pos"=4*s.history.length ∧
      Prefix (RamUnsignedBuffer.encode (MaskedMassData.flags (ResidualData.mask s.active))) "region.active" σ := by
      simpa only [RamRegionState.View,hs] using hview
    have hc : (Cond.eq (.var "region.phase") (.lit 1)).evalB B σ=some false := by
      rw [evalB_condEq (evalB_var (hvw.1 ▸ (by omega : 2 < B))) (evalB_lit (by omega)),hvw.1]
      rfl
    obtain ⟨τ,rr,pr⟩ := RamHistoryCut.history_spec B M I d s.history p hM (by omega) hB h4 (by omega) hindex hvertex hd hr
      hcuts htotal hp hv.2 (by simpa only [hseed,hdelta] using hv.1) σ
      ⟨hσ.nValue,hσ.n2Value,hvw.2.2.1,hσ.lengthData,hvw.2.1,hσ.weightsData,hσ.capacityData,htσ,
        hroom.potential _ (by simp [RamLargePotential.scratchArrays]),hroom.mask,hroom.crossing⟩
    have hcost : RamHistoryCut.cost n s.history.length M ≤ RamHistoryCut.cost n p M := by
      dsimp [RamHistoryCut.cost,RamHistoryPotential.cost]
      exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.mul_le_mul_right n (by omega)) 16) _
    exact ⟨τ,(Run.ite_false (c := RamLargeCut.command) hc rr).mono (by dsimp [cost,Cond.size,Expr.size]; omega),pr⟩
  | large e =>
    have hv : RegionLoop.LargeGood I (MetricMatrix.rational d) delta e.region := by
      simpa only [RegionRuntimeCorrespondence.ValidFinal,hs] using hvalid
    have hvw : σ.vars "region.phase"=1 ∧
      RamSmallRegion.Input (RadiusSearchData.atRadius (RegionExecutionData.query I d s.active e.root seed beta) e.radius)
        s.active s.history e.root σ := by simpa only [RamRegionState.View,hs] using hview
    let Tin := RamSmallRegion.ball (fun v => d v e.root) e.radius
    let Tout := RamSmallRegion.ball (d e.root) e.radius
    have hin : Tin.Nonempty := ⟨e.root,by simpa [Tin,RamSmallRegion.ball,RegionCharging.ball,hdiag,Entry.region] using hv.1⟩
    have hout : Tout.Nonempty := ⟨e.root,by simpa [Tout,RamSmallRegion.ball,RegionCharging.ball,hdiag,Entry.region] using hv.1⟩
    have hiMask : Prefix (RamUnsignedBuffer.encode (CutScoreData.vertexFlags Tin)) "region.inMask" σ := by
      simpa only [CutScoreData.vertexFlags,←RamSmallRegion.mask_eq,RadiusSearchData.atRadius,RegionExecutionData.query,RamRegionSetup.query,Tin] using hvw.2.masks.inMask
    have hoMask : Prefix (RamUnsignedBuffer.encode (CutScoreData.vertexFlags Tout)) "region.outMask" σ := by
      simpa only [CutScoreData.vertexFlags,←RamSmallRegion.mask_eq,RadiusSearchData.atRadius,RegionExecutionData.query,RamRegionSetup.query,Tout] using hvw.2.masks.outMask
    have hrad : (e.radius : ℚ) ≤ 1/(4*LargeBallRounding.total I^2) := by
      simpa only [Entry.region,hdelta,RegionRounding.radiusBudget] using hv.2.1
    have hc : (Cond.eq (.var "region.phase") (.lit 1)).evalB B σ=some true := by
      rw [evalB_condEq (evalB_var (hvw.1 ▸ (by omega : 1 < B))) (evalB_lit (by omega)),hvw.1]
      rfl
    obtain ⟨τ,rr,S,hadm,hratio,hmask⟩ := RamLargeCut.large_ball_spec B M I d Tin Tout hin hout e.root
      (hlargeBounds Tin Tout hin hout) hcuts hM hB hindex hvertex htotal hdiag hsep htri
      (fun v hv => ((Finset.mem_filter.mp hv).2.le).trans hrad)
      (fun v hv => ((Finset.mem_filter.mp hv).2.le).trans hrad)
      hv.2.2.2 hv.2.2.1 σ
      ⟨⟨hσ.nValue,hσ.weightsData,hσ.lengthData,hiMask,hoMask⟩,hσ.n2Value,htσ,hσ.capacityData,hroom.potential,hroom.mask,hroom.crossing⟩
    have hW : 0 ≤ RegionRounding.metricCost I (MetricMatrix.rational d) :=
      RegionCharging.weight_nonnegative _ _ (fun _ _ => NNRat.coe_nonneg _) (fun _ _ => NNRat.coe_nonneg _)
    have hk : (1 : ℚ) ≤ RegionBudget.steps p := by exact_mod_cast RegionBudget.steps_pos p
    have hmul := mul_le_mul_of_nonneg_right hk hW
    have hrat : CutSweeps.ratioQ I S ≤ 6*RegionRounding.metricCost I (MetricMatrix.rational d) := hratio
    refine ⟨τ,(Run.ite_true (d := RamHistoryCut.command) hc rr).mono (by dsimp [cost,Cond.size,Expr.size]; omega),S,hadm,?_,hmask⟩
    nlinarith

end Lax455465Proofs.RamRegionCut
