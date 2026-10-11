import Lax455465Proofs.RegionQueryHeight
import Lax455465Proofs.RamVolume
import Lax455465Proofs.RamBoundary

namespace Lax455465Proofs.RamRegionContext

open RegionQueryData Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamUnsignedScalar RamVirtualState
open scoped NNRat

structure Input {n : ℕ} (q : Query n) (σ : Env) : Prop where
  nValue : σ.vars "metric.n"=n
  n2Value : σ.vars "metric.n2"=n*n
  radiusData : Stored "region.radius" q.radius σ
  seedData : Stored "round.seed" q.seed σ
  betaData : Stored "round.slope" q.beta σ
  weightsData : Prefix (RamUnsignedBuffer.encode (List.ofFn q.weights)) "region.weights" σ
  capacityData : Prefix (RamUnsignedBuffer.encode (MetricMatrix.values q.capacity)) "region.capacities" σ
  lengthData : Prefix (RamUnsignedBuffer.encode (MetricMatrix.values q.length)) "metric.old" σ
  outData : Prefix (RamUnsignedBuffer.encode (List.ofFn q.outDistance)) "region.out" σ
  inData : Prefix (RamUnsignedBuffer.encode (List.ofFn q.inDistance)) "region.in" σ

def sourceVariables : List String := ["metric.n","metric.n2","region.radius.n","region.radius.d",
  "round.seed.n","round.seed.d","round.slope.n","round.slope.d"]
def arrays : List String := ["region.weights","region.capacities","metric.old","region.out","region.in"]

theorem Input.frame {B K : ℕ} {cmd : Com} {σ τ : Env} (hr : Run B cmd σ τ K)
    {n : ℕ} {q : Query n} (h : Input q σ)
    (hx : ∀ x ∈ sourceVariables, x ∉ cmd.wvars) (ha : ∀ a ∈ arrays, a ∉ cmd.warrs) : Input q τ := by
  refine ⟨(hr.frame_var _ (hx _ (by simp [sourceVariables]))).trans h.nValue,
    (hr.frame_var _ (hx _ (by simp [sourceVariables]))).trans h.n2Value,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Stored,String.reduceAppend,hr.frame_var "region.radius.n" (hx _ (by simp [sourceVariables])),hr.frame_var "region.radius.d" (hx _ (by simp [sourceVariables]))] using h.radiusData
  · simpa only [Stored,String.reduceAppend,hr.frame_var "round.seed.n" (hx _ (by simp [sourceVariables])),hr.frame_var "round.seed.d" (hx _ (by simp [sourceVariables]))] using h.seedData
  · simpa only [Stored,String.reduceAppend,hr.frame_var "round.slope.n" (hx _ (by simp [sourceVariables])),hr.frame_var "round.slope.d" (hx _ (by simp [sourceVariables]))] using h.betaData
  · simpa only [Prefix,hr.frame_arr "region.weights" (ha _ (by simp [arrays]))] using h.weightsData
  · simpa only [Prefix,hr.frame_arr "region.capacities" (ha _ (by simp [arrays]))] using h.capacityData
  · simpa only [Prefix,hr.frame_arr "metric.old" (ha _ (by simp [arrays]))] using h.lengthData
  · simpa only [Prefix,hr.frame_arr "region.out" (ha _ (by simp [arrays]))] using h.outData
  · simpa only [Prefix,hr.frame_arr "region.in" (ha _ (by simp [arrays]))] using h.inData

theorem Input.ballContext {n : ℕ} {q : Query n} {σ : Env} (h : Input q σ) (b : Bool) :
    RamBallMass.Context b q.weights (distance q b) q.radius σ := by
  refine ⟨h.nValue,h.radiusData,h.weightsData,?_⟩
  cases b with
  | false => exact h.inData
  | true => exact h.outData

theorem Input.volumeContext {n : ℕ} {q : Query n} {σ : Env} (h : Input q σ) (b : Bool) :
    RamVolume.Context b q.capacity q.length (distance q b) q.seed q.radius σ := by
  refine ⟨h.nValue,h.n2Value,h.radiusData,h.seedData,h.capacityData,h.lengthData,?_⟩
  cases b with
  | false => exact h.inData
  | true => exact h.outData

structure Masks {n : ℕ} (q : Query n) (σ : Env) : Prop where
  input : Input q σ
  outMask : Prefix (RamUnsignedBuffer.encode (BallMassData.mask q.outDistance q.radius)) "region.outMask" σ
  inMask : Prefix (RamUnsignedBuffer.encode (BallMassData.mask q.inDistance q.radius)) "region.inMask" σ
  directionValue : σ.vars "region.outward" = if direction q q.radius then 1 else 0

theorem Masks.boundaryContext {n : ℕ} {q : Query n} {σ : Env} (h : Masks q σ) (b : Bool) :
    RamBoundary.Context b q.capacity (distance q b) q.radius σ := by
  refine ⟨h.input.nValue,h.input.n2Value,h.input.capacityData,?_⟩
  cases b with
  | false => exact h.inMask
  | true => exact h.outMask

theorem num_bound {M : ℕ} {q : ℚ≥0} (h : LpInputSize.Height M (q : ℚ)) : q.num ≤ M := by
  simpa only [NNRat.natAbs_num_coe] using h.1

theorem den_bound {M : ℕ} {q : ℚ≥0} (h : LpInputSize.Height M (q : ℚ)) : q.den ≤ M := by
  simpa only [NNRat.den_coe] using h.2

theorem mass_height {n : ℕ} (q : Query n) (H : ℕ) (hb : RegionQueryHeight.Bounds q H) (b : Bool) :
    LpInputSize.Height (2^H) (BallMassData.mass q.weights (distance q b) q.radius : ℚ) := by
  have hh := hb.massPrefixBound b (RamMaskedSum.coefficients (List.ofFn q.weights) (BallMassData.mask (distance q b) q.radius)).length
  simpa only [List.take_length,BallMassData.mass] using hh

end Lax455465Proofs.RamRegionContext
