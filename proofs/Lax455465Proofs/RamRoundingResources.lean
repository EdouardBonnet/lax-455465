import Lax455465Proofs.RamRoundingBudget
import Lax455465Proofs.RamMetricCostResources

namespace Lax455465Proofs.RamRoundingResources
open Lax455465.RationalEncoding Lax455465.ProductNetwork Lax759944.BinaryWordEncoding
open LpInputSize RamRoundingBudget
open scoped NNRat

/-- The native instruction bound written as a polynomial expression in
vertex count and the three rational bit budgets. -/
def timeExpression {α : Type*} [Semiring α] (n w c h v : α) : α :=
  let a := c*2+1
  let b := v*2+1
  let query := (288*h+880)*(n*n)+(144*h+584)*n+144*h+554
  let prelude := (36*a+208)*(n*n)+(36*a+166)*n+40
  let setup := (36*a+query+160)*(2*n+4+1+2*n)+84*n+query+80
  let core := prelude+setup+96*n+200
  let loop := (core+13)*(n+1)+6
  let score := (36*b+234)*(n*n)+(36*b+152)*n+144*b+468
  let candidate := score+110*n+30
  let sweep := (candidate+92)*n+candidate+16
  let setPotential := (168*n+46)*n+8+48*n+18
  let average := (72*b+224)*n+22
  let large := 2*setPotential+2*average+24*n+80+sweep+2
  let history := (140*n+74)*n+16+sweep
  let regionCut := large+history+4
  let zero := 98*(n*n)+66*n+38+sweep
  ((36*a+200)*(n+1)+600*a+2000)+(36*(w+3)+28*n+116+loop+regionCut+zero)

theorem time_bound (n p w : ℕ) (total : ℚ≥0) (hp : p ≤ n) (ht : total.den ≤ 2^w) :
    RamRoundingBudget.cost n p w total ≤ timeExpression n w (constants w) (queries n w) (cuts n w) := by
  have hk := RamRoundingBudget.steps_le hp
  have hs : (total.den*3).size ≤ w+3 := by
    apply Nat.size_le.mpr
    calc
      total.den*3 ≤ 2^w*3 := Nat.mul_le_mul_right 3 ht
      _ < 2^(w+3) := by rw [pow_add]; have := Nat.two_pow_pos w; norm_num
  simp only [RamRoundingBudget.cost,RamRegionBoundedLoop.cost,RamRegionCore.cost,RamRegionPrelude.cost,
    RamRegionSetup.cost,RamRadiusSearch.queryCost,RamRegionCut.cost,RamLargeCut.cost,RamLargePotential.cost,
    RamSetPotential.cost,RamSetDistances.cost,RamPotentialAverage.cost,RamHistoryCut.cost,RamHistoryPotential.cost,
    RamZeroCut.cost,RamZeroCut.prepareCost,RamPotentialSweep.cost,RamThresholdCandidate.cost,RamCutScore.cost,
    ←pow_mul,Nat.size_pow,timeExpression]
  gcongr

noncomputable def baseBound (metricWord : Polynomial ℕ) : Polynomial ℕ :=
  RamMetricCostResources.heightBound metricWord+Polynomial.X*(Polynomial.X+1)+Polynomial.X+1+
    metricWord+3*Polynomial.X+8

noncomputable def constantsBound (base : Polynomial ℕ) : Polynomial ℕ := 3*base+2
noncomputable def queriesBound (base : Polynomial ℕ) : Polynomial ℕ :=
  let c := constantsBound base
  2*(3*(4*(2*c)*(Polynomial.X*Polynomial.X+1)+Polynomial.X*Polynomial.X+1)+1)+2*c+1
noncomputable def cutsBound (base : Polynomial ℕ) : Polynomial ℕ :=
  let c := constantsBound base
  2*c+3*(c*(Polynomial.X*Polynomial.X+1)+Polynomial.X*Polynomial.X+1)+
    (2*c*(Polynomial.X+1)+Polynomial.X+1)+2*Polynomial.X+4
noncomputable def wordBound (base : Polynomial ℕ) : Polynomial ℕ :=
  2*(constantsBound base+queriesBound base+cutsBound base)+2*Polynomial.X*Polynomial.X+12*Polynomial.X+28
noncomputable def timeBound (base : Polynomial ℕ) : Polynomial ℕ :=
  timeExpression Polynomial.X base (constantsBound base) (queriesBound base) (cutsBound base)

theorem eval_constants (base : Polynomial ℕ) (L : ℕ) :
    (constantsBound base).eval L=constants (base.eval L) := by
  simp [constantsBound,constants,RoundingHeight.constantExponent]
theorem eval_queries (base : Polynomial ℕ) (L : ℕ) :
    (queriesBound base).eval L=queries L (base.eval L) := by
  simp [queriesBound,eval_constants,queries,RegionIterationHeight.exponent,RegionQueryHeight.exponent,
    VolumeHeight.exponent,VolumeHeight.sumExponent]
theorem eval_cuts (base : Polynomial ℕ) (L : ℕ) :
    (cutsBound base).eval L=cuts L (base.eval L) := by
  simp [cutsBound,eval_constants,cuts,RoundingHeight.cutExponent,CutScoreHeight.exponent,
    CutScoreHeight.sumExponent,LargePotentialData.exponent]
theorem eval_word (base : Polynomial ℕ) (L : ℕ) :
    (wordBound base).eval L=width L (base.eval L) := by
  simp [wordBound,eval_constants,eval_queries,eval_cuts,width,RamHostBounds.sufficient]
  omega
theorem eval_time (base : Polynomial ℕ) (L : ℕ) :
    (timeBound base).eval L=timeExpression L (base.eval L) (constants (base.eval L))
      (queries L (base.eval L)) (cuts L (base.eval L)) := by
  simp only [timeBound,timeExpression,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,
    Polynomial.eval_X,Polynomial.eval_one,eval_constants,eval_queries,eval_cuts]

theorem width_mono {n m w : ℕ} (hn : n ≤ m) : width n w ≤ width m w := by
  dsimp [width,RamHostBounds.sufficient,queries,RegionIterationHeight.exponent,RegionQueryHeight.exponent,
    VolumeHeight.exponent,VolumeHeight.sumExponent,cuts,RoundingHeight.cutExponent,CutScoreHeight.exponent,
    CutScoreHeight.sumExponent,LargePotentialData.exponent]
  gcongr

theorem time_mono {n m w : ℕ} (hn : n ≤ m) :
    timeExpression n w (constants w) (queries n w) (cuts n w) ≤
      timeExpression m w (constants w) (queries m w) (cuts m w) := by
  dsimp [timeExpression,queries,RegionIterationHeight.exponent,RegionQueryHeight.exponent,
    VolumeHeight.exponent,VolumeHeight.sumExponent,cuts,RoundingHeight.cutExponent,CutScoreHeight.exponent,
    CutScoreHeight.sumExponent,LargePotentialData.exponent]
  gcongr

end Lax455465Proofs.RamRoundingResources
