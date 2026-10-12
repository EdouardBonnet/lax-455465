import Lax455465Proofs.RoundingHeight
import Lax455465Proofs.RamHostBounds

set_option maxRecDepth 8192
namespace Lax455465Proofs.RamRoundingBudget
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRegionContext
open Lax455465.RationalEncoding LpInputSize
open scoped NNRat

def constants (w : ℕ) : ℕ := RoundingHeight.constantExponent w
def queries (n w : ℕ) : ℕ := RegionIterationHeight.exponent n (constants w)
def cuts (n w : ℕ) : ℕ := RoundingHeight.cutExponent n (constants w)
def width (n w : ℕ) : ℕ := RamHostBounds.sufficient (constants w+queries n w+cuts n w) 0 0 (2*n*n+12*n+20)

def cost (n p w : ℕ) (total : ℚ≥0) : ℕ :=
  ((36*((2^(constants w))^2).size+200)*(n+1)+600*((2^(constants w))^2).size+2000)+
    (36*(total.den*3).size+28*n+116+RamRegionBoundedLoop.cost n p (2^(constants w)) (queries n w)+
      RamRegionCut.cost n p (2^(cuts n w))+RamZeroCut.cost n (2^(cuts n w)))

theorem support_le {n : ℕ} (I : RationalInstance n) : RamRoundingInit.support I.weight ≤ n := by
  unfold RamRoundingInit.support RegionSelection.support
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans (by simp)

theorem steps_le {n p : ℕ} (hp : p ≤ n) : RegionBudget.steps p ≤ 2*n+4 := by
  have := Nat.log2_le_self p
  unfold RegionBudget.steps
  omega

theorem host_bounds (n w W : ℕ) (hW : width n w ≤ W) :
    2*(2^(constants w))^2+3 < 2^W ∧ 2*(2^(queries n w))^2+3 < 2^W ∧
      2*(2^(cuts n w))^2+3 < 2^W ∧ 2*n*n+12*n+21 < 2^W := by
  obtain ⟨hb,_,_,hi⟩ := RamHostBounds.sufficient_bounds _ 0 0 _ W hW
  have hw := Nat.pow_le_pow_right (show 1 ≤ 2 by decide)
    (show constants w ≤ constants w+queries n w+cuts n w by omega)
  have hq := Nat.pow_le_pow_right (show 1 ≤ 2 by decide)
    (show queries n w ≤ constants w+queries n w+cuts n w by omega)
  have hc := Nat.pow_le_pow_right (show 1 ≤ 2 by decide)
    (show cuts n w ≤ constants w+queries n w+cuts n w by omega)
  refine ⟨?_,?_,?_,hi⟩
  all_goals
    apply lt_of_le_of_lt _ hb
    gcongr

set_option maxHeartbeats 3200000 in
/-- All runtime branches use these uniform budgets. The assumptions concern
only the original data, its cost, and the prefixes of the original weight
vector; no bounds on selected radii, regions, cuts, or histories are assumed. -/
theorem command_spec (W w : ℕ) {n : ℕ} (I : RationalInstance n) (d : MetricMatrix.Matrix n)
    (hw : 2*n+4 ≤ w) (hW : width n w ≤ W)
    (hweights : ∀ v,Height (2^w) (I.weight v : ℚ))
    (hcapacities : ∀ u v,Height (2^w) (I.capacity u v : ℚ))
    (hdistances : ∀ u v,Height (2^w) (d u v : ℚ))
    (hcost : Height (2^w) (MetricCostData.cost I d : ℚ))
    (hprefix : ∀ i,Height (2^w) (((List.ofFn I.weight).take i).sum : ℚ))
    (hp : 0 < RamRoundingInit.support I.weight) (htotal : 0 < LargeBallRounding.total I)
    (hdiag : ∀ v,d v v=0)
    (htri : ∀ u v t,(d u t : ℚ) ≤ (d u v : ℚ)+(d v t : ℚ))
    (hsep : 1 ≤ LargeBallRounding.distanceSeparation I (MetricMatrix.rational d)) :
    Spec (2^W) (fun σ => RamMetricRounding.Input I d σ ∧
      RamRegionInvariant.Room n (RamRoundingInit.support I.weight) σ ∧ RamRegionCut.Room n σ)
      RamMetricRounding.command (fun _ τ => RamRegionCut.Output I d (RamRoundingInit.support I.weight) τ)
      (cost n (RamRoundingInit.support I.weight) w (RamRoundingInit.total I.weight)) := by
  let p := RamRoundingInit.support I.weight
  let total := RamRoundingInit.total I.weight
  let seed := RoundingConstants.seed (MetricCostData.cost I d) p
  let delta := RoundingConstants.delta total
  let beta := RoundingConstants.beta total p
  have hpN : p ≤ n := support_le I
  have hk : RegionBudget.steps p ≤ 2*n+4 := steps_le hpN
  have hpow : 2^w ≤ 2^(constants w) := Nat.pow_le_pow_right (by decide) (by
    dsimp [constants,RoundingHeight.constantExponent]; omega)
  have widen {q : ℚ} (h : Height (2^w) q) : Height (2^(constants w)) q := height_mono h hpow
  have ht : Height (2^w) (total : ℚ) := by
    have h := hprefix (List.ofFn I.weight).length
    simpa only [List.take_length,total,RamRoundingInit.total,List.sum_ofFn] using h
  have hconstants := RoundingHeight.constant_bounds (MetricCostData.cost I d) total p w (by omega) hcost ht
    (by have := Nat.lt_two_pow_self (n := w); omega) (by have := Nat.lt_two_pow_self (n := w); omega)
  have hM : 4 ≤ 2^(constants w) := (by norm_num : 4 ≤ 2^2).trans
    (Nat.pow_le_pow_right (by decide) (by dsimp [constants,RoundingHeight.constantExponent]; omega))
  have hkM : RegionBudget.steps p ≤ 2^(constants w) := by
    have := Nat.lt_two_pow_self (n := w); omega
  obtain ⟨hB,hquery,hNB,hindex⟩ := host_bounds n w W hW
  obtain ⟨hMN,hpN',hcuts,hlarge⟩ := RoundingHeight.cut_bounds I d (constants w) p hpN
    (fun v => widen (hweights v)) (fun u v => widen (hcapacities u v)) (fun u v => widen (hdistances u v))
  have hthreshold : Height (2^(queries n w)) (RamLargeThreshold.threshold total : ℚ) := by
    have hh := height_mul ht (show Height 3 ((2/3 : ℚ≥0) : ℚ) from by norm_num [Height])
    have hmul : 2^w*3 ≤ 2^(w+2) := by rw [pow_add]; norm_num
    have hexp : w+2 ≤ queries n w := by
      dsimp [queries,RegionIterationHeight.exponent,RegionQueryHeight.exponent,VolumeHeight.exponent,
        constants,RoundingHeight.constantExponent]
      omega
    exact height_mono (by simpa only [RamLargeThreshold.threshold,NNRat.coe_mul] using hh)
      (hmul.trans (Nat.pow_le_pow_right (by decide) hexp))
  have htCoe : (total : ℚ)=LargeBallRounding.total I := RegionRuntimeCorrespondence.coe_total I
  have hdCoe : (delta : ℚ)=RegionRounding.radiusBudget I := by
    dsimp only [delta]
    rw [RoundingConstants.coe_delta,htCoe]
    rfl
  have hdelta : 0 < (delta : ℚ) := by rw [hdCoe,RegionRounding.radiusBudget]; positivity
  have hseed : (seed : ℚ)=RegionRounding.metricCost I (MetricMatrix.rational d)/(p : ℚ) := by
    simp only [seed,RoundingConstants.seed,NNRat.coe_div,NNRat.coe_natCast,MetricCostData.coe_cost]
  have hcostSeed : RegionRounding.metricCost I (MetricMatrix.rational d) ≤ (p : ℚ)*(seed : ℚ) := by
    rw [hseed,mul_div_cancel₀ _ (by exact_mod_cast (show p ≠ 0 by omega))]
  have hsupport : (RegionSelection.support (RegionLoop.weights I Finset.univ)).card ≤ p := by
    change (RegionSelection.support (fun v => if v ∈ (Finset.univ : Finset (Fin n)) then (I.weight v : ℚ) else 0)).card ≤ p
    simp only [Finset.mem_univ,if_true]
    exact Nat.le_refl _
  apply RamMetricRounding.command_spec (2^W) (2^(constants w)) (queries n w) (2^(cuts n w)) I d seed beta delta p
    hM hkM hB hquery (by nlinarith) (by omega) (by omega) (by omega) hthreshold
    (fun v => num_bound (widen (hweights v))) (fun v => den_bound (widen (hweights v)))
    (fun u v => num_bound (widen (hcapacities u v))) (fun u v => den_bound (widen (hcapacities u v)))
    (fun u v => widen (hdistances u v)) hconstants.deltaBound hconstants.stepBound
    _ (RoundingConstants.coe_beta total p) hdelta hp hdiag htri hcostSeed hsupport (widen ht)
    Nat.one_le_two_pow (by simpa only [constants,cuts] using hMN) (by simpa only [constants,cuts] using hpN') hNB
    hlarge hcuts htotal hsep hseed hdCoe rfl hconstants (fun i => widen (hprefix i))
  intro active root i hi
  exact RegionIterationHeight.bounds I d seed beta delta (RegionBudget.steps p) (constants w)
    (fun v => widen (hweights v)) (fun u v => widen (hcapacities u v)) (fun u v => widen (hdistances u v))
    hconstants.seedBound hconstants.betaBound hconstants.deltaBound hconstants.stepBound hkM active root _
    (List.getElem_mem hi)

end Lax455465Proofs.RamRoundingBudget
