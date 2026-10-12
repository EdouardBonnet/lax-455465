import Lax455465Proofs.RamCutScore
import Lax455465Proofs.ThresholdCutData
import Lax455465Proofs.RamBestUpdate

set_option maxRecDepth 4096
namespace Lax455465Proofs.RamThresholdCandidate
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar RamRegionContext
open Lax455465.RationalEncoding
open scoped NNRat

structure Input {n : ℕ} (I : RationalInstance n) (potential : Fin n → ℚ≥0) (reversed : Bool) (σ : Env) : Prop where
  nValue : σ.vars "metric.n"=n
  n2Value : σ.vars "metric.n2"=n*n
  count : σ.vars "cut.count"=n
  reversedValue : σ.vars "cut.reversed"=(if reversed then 1 else 0)
  totalData : Stored "round.total" (RamRoundingInit.total I.weight) σ
  weightsData : Prefix (RamUnsignedBuffer.encode (List.ofFn I.weight)) "flow.weights" σ
  capacityData : Prefix (RamUnsignedBuffer.encode (MetricMatrix.values I.capacity)) "flow.capacities" σ
  potentialData : Prefix (RamUnsignedBuffer.encode (List.ofFn potential)) "cut.potential" σ
  maskRoom : 2*n<(σ.arrs "cut.flags").length
  crossingRoom : 2*(n*n)<(σ.arrs "cut.crossing").length

def names : List String := ["metric.n","metric.n2","cut.count","cut.reversed","round.total.n","round.total.d"]
def arrays : List String := ["flow.weights","flow.capacities","cut.potential"]

theorem Input.frame {B K : ℕ} {cmd : Com} {σ τ : Env} (rr : Run B cmd σ τ K)
    {n : ℕ} {I : RationalInstance n} {potential : Fin n → ℚ≥0} {reversed : Bool} (h : Input I potential reversed σ)
    (hx : ∀ x∈names,x∉cmd.wvars) (ha : ∀ a∈arrays,a∉cmd.warrs) : Input I potential reversed τ := by
  exact ⟨(rr.frame_var _ (hx _ (by simp [names]))).trans h.nValue,
    (rr.frame_var _ (hx _ (by simp [names]))).trans h.n2Value,
    (rr.frame_var _ (hx _ (by simp [names]))).trans h.count,
    (rr.frame_var _ (hx _ (by simp [names]))).trans h.reversedValue,
    RamRoundingConstants.storedFrame rr h.totalData (hx _ (by simp [names])) (hx _ (by simp [names])),
    by simpa only [Prefix,rr.frame_arr "flow.weights" (ha _ (by simp [arrays]))] using h.weightsData,
    by simpa only [Prefix,rr.frame_arr "flow.capacities" (ha _ (by simp [arrays]))] using h.capacityData,
    by simpa only [Prefix,rr.frame_arr "cut.potential" (ha _ (by simp [arrays]))] using h.potentialData,
    by rw [RamFrames.run_array_length rr "cut.flags"]; exact h.maskRoom,
    by rw [RamFrames.run_array_length rr "cut.crossing"]; exact h.crossingRoom⟩

def mask : Com := .ite (.eq (.var "cut.reversed") (.lit 1))
  (RamThresholdMask.command true) (RamThresholdMask.command false)
def command : Com := .seq (RamArrayScalar.command "cut.potential" "cut.candidate" "cut.threshold")
  (.seq mask RamCutScore.command)
def cost (n M : ℕ) : ℕ := RamCutScore.cost n M+110*n+30

set_option maxHeartbeats 3200000 in
/-- Load the current vertex's actual potential as threshold, construct its
normal or reversed shore, and compute its exact admissibility and ratio. -/
theorem command_spec (B M : ℕ) {n : ℕ} (I : RationalInstance n) (potential : Fin n → ℚ≥0) (reversed : Bool)
    (i : ℕ) (hi : i<n) (hM : 1≤M) (hB : 2*M^2+3<B) (hindex : 2*(n*n)+2<B) (hvertex : 2*n+2<B)
    (hp : ∀ v,LpInputSize.Height M (potential v : ℚ))
    (hb : CutScoreHeight.Bounds I (ThresholdCutData.candidate reversed potential i) M) :
    Spec B (fun σ => Input I potential reversed σ ∧ σ.vars "cut.candidate"=i) command
      (fun _ τ => Input I potential reversed τ ∧
        RamBestUpdate.Current (ThresholdCutData.valid I reversed potential) (ThresholdCutData.score I reversed potential) i τ ∧
        Prefix (RamUnsignedBuffer.encode (CutScoreData.vertexFlags (ThresholdCutData.candidate reversed potential i))) "cut.flags" τ)
      (cost n M) := by
  have hMB : M<B := by nlinarith
  let v : Fin n := ⟨i,hi⟩
  let S := ThresholdCutData.candidate reversed potential i
  have hS : S=ThresholdCutData.shore reversed potential (potential v) := ThresholdCutData.at_eq reversed potential i hi
  have hmask : MaskedMassData.flags (fun u => RamThresholdMask.chosen reversed (potential u) (potential v))=CutScoreData.vertexFlags S := by
    rw [hS]
    exact ThresholdCutData.mask_eq reversed potential (potential v)
  rintro σ ⟨hσ,hidx⟩
  have hi' : i<(List.ofFn potential).length := by simpa only [List.length_ofFn] using hi
  have he : (List.ofFn potential)[i]=potential v := by simp [v]
  obtain ⟨σ1,r1,p1⟩ := RamArrayScalar.command_spec B "cut.potential" "cut.candidate" "cut.threshold" (List.ofFn potential) i hi'
    (by nlinarith) (by omega) (by rw [he]; exact (num_bound (hp v)).trans_lt hMB)
    (by rw [he]; exact (den_bound (hp v)).trans_lt hMB) (by decide) (by decide) σ ⟨hσ.potentialData,hidx⟩
  have h1 := Input.frame r1 hσ (by dsimp [names]; decide) (by dsimp [arrays]; decide)
  have maskSpec : ∃ σ2,Run B mask σ1 σ2 (110*n+12) ∧ Prefix (RamUnsignedBuffer.encode (CutScoreData.vertexFlags S)) "cut.flags" σ2 := by
    have applyMask (b : Bool) : ∃ σ2,Run B (RamThresholdMask.command b) σ1 σ2 (110*n+8) ∧
        Prefix (RamUnsignedBuffer.encode (MaskedMassData.flags (fun u => RamThresholdMask.chosen b (potential u) (potential v)))) "cut.flags" σ2 := by
      obtain ⟨σ2,rr,pr⟩ := RamThresholdMask.command_spec B M b potential (potential v) hB hvertex
        (fun u => num_bound (hp u)) (fun u => den_bound (hp u)) (num_bound (hp v)) (den_bound (hp v)) σ1
        ⟨⟨h1.nValue,by simpa only [he] using p1,h1.potentialData⟩,h1.maskRoom⟩
      exact ⟨σ2,rr,pr.2⟩
    cases hr : reversed
    · have hv : σ1.vars "cut.reversed"=0 := by simpa only [hr,Bool.false_eq_true,if_false] using h1.reversedValue
      have hc : (Cond.eq (.var "cut.reversed") (.lit 1)).evalB B σ1=some false := by
        rw [evalB_condEq (evalB_var (hv ▸ (by omega : 0<B))) (evalB_lit (by nlinarith)),hv]
        rfl
      obtain ⟨σ2,rr,pr⟩ := applyMask false
      exact ⟨σ2,(Run.ite_false (c := RamThresholdMask.command true) hc rr).mono (by dsimp [Cond.size,Expr.size]; omega),
        by rw [←hmask,hr]; exact pr⟩
    · have hv : σ1.vars "cut.reversed"=1 := by simpa only [hr,if_true] using h1.reversedValue
      have hc : (Cond.eq (.var "cut.reversed") (.lit 1)).evalB B σ1=some true := by
        rw [evalB_condEq (evalB_var (hv ▸ (by nlinarith : 1<B))) (evalB_lit (by nlinarith)),hv]
        rfl
      obtain ⟨σ2,rr,pr⟩ := applyMask true
      exact ⟨σ2,(Run.ite_true (d := RamThresholdMask.command false) hc rr).mono (by dsimp [Cond.size,Expr.size]; omega),
        by rw [←hmask,hr]; exact pr⟩
  obtain ⟨σ2,r2,p2⟩ := maskSpec
  have h2 := Input.frame r2 h1 (by dsimp [names]; decide) (by dsimp [arrays]; decide)
  obtain ⟨τ,r3,p3⟩ := RamCutScore.command_spec B M I S hM hb hB hindex hvertex σ2
    ⟨⟨h2.nValue,h2.n2Value,h2.totalData,h2.weightsData,h2.capacityData,p2⟩,h2.crossingRoom⟩
  have rr := r1.seq (r2.seq r3)
  exact ⟨τ,rr.mono (by dsimp [cost]; omega),Input.frame rr hσ (by dsimp [names]; decide) (by dsimp [arrays]; decide),
    ⟨(rr.frame_var _ (by decide)).trans hidx,p3.2.2,p3.2.1⟩,p3.1.maskData⟩

end Lax455465Proofs.RamThresholdCandidate
