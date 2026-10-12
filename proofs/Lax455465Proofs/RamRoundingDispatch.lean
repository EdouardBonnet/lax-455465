import Lax455465Proofs.RamPositiveRounding
import Lax455465Proofs.RamZeroCut
import Lax455465Proofs.MetricCostData

set_option maxRecDepth 8192
namespace Lax455465Proofs.RamRoundingDispatch
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamUnsignedScalar RamRegionInvariant RamRegionContext
open Lax455465.RationalEncoding
open scoped NNRat BigOperators

def command : Com := .ite (.eq (.var "round.cost.n") (.lit 0)) RamZeroCut.command RamPositiveRounding.command

set_option maxHeartbeats 6400000 in
/-- The exact cost numerator selects zero-cost rounding or region growth;
both branches return an admissible cut with the common quantitative bound. -/
theorem command_spec (B M H N : ℕ) {n : ℕ} (I : RationalInstance n) (length : MetricMatrix.Matrix n)
    (seed beta delta : ℚ≥0) (p : ℕ)
    (hM : 3≤M) (hk : RegionBudget.steps p≤M) (hB : 2*M^2+3<B) (hquery : 2*(2^H)^2+3<B)
    (hindex : 2*(n*n)+2<B) (hvertex : 2*n+2<B) (hradius : 2*(RegionBudget.steps p+1+2*n)+2<B)
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
    (hcostHeight : LpInputSize.Height N (MetricCostData.cost I length : ℚ)) :
    Spec B (fun σ => RamRegionBegin.Source I length seed beta delta p σ ∧ Room n p σ ∧ RamRegionCut.Room n σ ∧
      Stored "round.cost" (MetricCostData.cost I length) σ)
      command (fun _ τ => RamRegionCut.Output I length p τ)
      (36*((RamRoundingInit.total I.weight).den*3).size+28*n+116+
        RamRegionBoundedLoop.cost n p M H+RamRegionCut.cost n p N+RamZeroCut.cost n N) := by
  rintro σ ⟨hσ,hregionRoom,hcutRoom,hcostσ⟩
  have hNB' : N < B := by nlinarith
  have hMN' : M ≤ N := by nlinarith
  have hnσ : σ.vars "round.cost.n"=(MetricCostData.cost I length).num := hcostσ.1
  have hnum : (MetricCostData.cost I length).num < B := (num_bound hcostHeight).trans_lt hNB'
  by_cases hz : (MetricCostData.cost I length).num=0
  · have hcost0 : MetricCostData.cost I length=0 := by
      rw [←NNRat.num_div_den (MetricCostData.cost I length),hz]
      simp
    have hW0 : RegionRounding.metricCost I (MetricMatrix.rational length)=0 := by
      rw [←MetricCostData.coe_cost,hcost0]; rfl
    have hc : (Cond.eq (.var "round.cost.n") (.lit 0)).evalB B σ=some true := by
      rw [evalB_condEq (evalB_var (hnσ ▸ hnum)) (evalB_lit (by omega)),hnσ,hz]
      rfl
    have hwN : ∀ v,LpInputSize.Height N (I.weight v : ℚ) := by
      intro v
      exact ⟨by simpa only [NNRat.natAbs_num_coe] using (hwn v).trans hMN',
        by simpa only [NNRat.den_coe] using (hwd v).trans hMN'⟩
    have hdN := fun u v => LpInputSize.height_mono (hl u v) hMN'
    have room0 : RamZeroCut.Room n σ := by
      refine ⟨?_,hcutRoom.crossing⟩
      intro a ha
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl | rfl | rfl
      · exact hcutRoom.potential _ (by simp [RamLargePotential.scratchArrays])
      · exact hcutRoom.potential _ (by simp [RamLargePotential.scratchArrays])
      · exact hcutRoom.mask
    obtain ⟨τ,rr,S,hadm,hratio,hmask⟩ := RamZeroCut.command_spec B N I length hN hNB hindex hvertex hwN hdN hcuts
      hdiag htri hsep hW0 σ
      ⟨⟨hσ.nValue,hσ.n2Value,hσ.weightsData,hσ.capacityData,hσ.lengthData,hσ.totalData⟩,room0⟩
    refine ⟨τ,(Run.ite_true (d := RamPositiveRounding.command) hc rr).mono (by dsimp [Cond.size,Expr.size]; omega),S,hadm,?_,hmask⟩
    simpa only [hW0,mul_zero] using hratio
  · have hWpos : 0 < RegionRounding.metricCost I (MetricMatrix.rational length) := by
      rw [←MetricCostData.coe_cost]
      have hcostNe : MetricCostData.cost I length ≠ 0 := by
        intro h; apply hz; rw [h]; rfl
      exact NNRat.coe_pos.mpr (lt_of_le_of_ne zero_le (Ne.symm hcostNe))
    have hseedPos : 0 < (seed : ℚ) := by rw [hseedEq]; exact div_pos hWpos (by exact_mod_cast hp)
    have hc : (Cond.eq (.var "round.cost.n") (.lit 0)).evalB B σ=some false := by
      rw [evalB_condEq (evalB_var (hnσ ▸ hnum)) (evalB_lit (by omega)),hnσ]
      simp [hz]
    obtain ⟨τ,rr,pr⟩ := RamPositiveRounding.command_spec B M H N I length seed beta delta p hM hk hB hquery hindex hvertex
      hradius hlen hthreshold hwn hwd hcn hcd hl hd hu hb hbeta hseedPos hdelta hp hdiag htri hcost hsupport htotal
      hN hMN hpN hNB hlargeBounds hcuts htotalPos hsep hseedEq hdeltaEq σ ⟨hσ,hregionRoom,hcutRoom⟩
    exact ⟨τ,(Run.ite_false (c := RamZeroCut.command) hc rr).mono (by dsimp [Cond.size,Expr.size]; omega),pr⟩

end Lax455465Proofs.RamRoundingDispatch
