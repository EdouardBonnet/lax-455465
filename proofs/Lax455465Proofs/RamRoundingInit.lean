import Lax455465Proofs.RamRoundingConstants
import Lax455465Proofs.RamSupport
import Lax455465Proofs.RamGridBudget
import Lax455465Proofs.RamArraySum

namespace Lax455465Proofs.RamRoundingInit
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamUnsignedScalar RamRegionContext RamVirtualState RoundingConstants
open scoped NNRat

def total {n : ℕ} (weights : Fin n → ℚ≥0) : ℚ≥0 := (List.ofFn weights).sum
def support {n : ℕ} (weights : Fin n → ℚ≥0) : ℕ := (RegionSelection.support (fun v => (weights v : ℚ))).card

structure Input {n : ℕ} (weights : Fin n → ℚ≥0) (cost : ℚ≥0) (σ : Env) : Prop where
  nValue : σ.vars "metric.n"=n
  weightsData : Prefix (RamUnsignedBuffer.encode (List.ofFn weights)) "flow.weights" σ
  costData : Stored "round.cost" cost σ

def command : Com := .seq (.assign "sum.count" (.var "metric.n"))
  (.seq (RamArraySum.command "flow.weights") (.seq (save "round.total")
    (.seq RamSupport.command (.seq RamGridBudget.command RamRoundingConstants.command))))

set_option maxHeartbeats 2400000 in
/-- Sum the original weights, count their positive support, compute the grid
budget, and initialize all region-growth constants from the existing metric
cost. The command reads the original weight buffer and uses no extra input. -/
theorem command_spec (B M : ℕ) {n : ℕ} (weights : Fin n → ℚ≥0) (cost : ℚ≥0)
    (hb : RoundingConstantHeight.Bounds cost (total weights) (support weights) M)
    (hM : 4≤M) (hB : 2*M^2+3<B) (hindex : 2*n+4<B) (hp : 0<support weights)
    (hw : ∀ v, LpInputSize.Height M (weights v : ℚ))
    (hs : ∀ i, LpInputSize.Height M (((List.ofFn weights).take i).sum : ℚ)) :
    Spec B (Input weights cost) command (fun _ τ => Input weights cost τ ∧
      RamRoundingConstants.Input cost (total weights) (support weights) τ ∧
      Stored "round.seed" (seed cost (support weights)) τ ∧
      Stored "round.delta" (delta (total weights)) τ ∧
      Stored "round.slope" (beta (total weights) (support weights)) τ ∧
      Stored "round.gridStep" (gridStep (total weights) (support weights)) τ)
      ((36*(M^2).size+200)*(n+1)+600*(M^2).size+2000) := by
  have hMB : M<B := by nlinarith
  have hpN : support weights≤n := by
    rw [support,←SupportData.count_support]
    exact (SupportData.count_le _).trans (by simp)
  have hsize : (support weights).size≤n :=
    (Nat.size_le.mpr Nat.lt_two_pow_self).trans hpN
  rintro σ hσ
  let ν := σ.setVar "sum.count" n
  have rstart : Run B (.assign "sum.count" (.var "metric.n")) σ ν 2 :=
    Run.assign (by rw [evalB_var_iff]; exact ⟨hσ.nValue.symm,hσ.nValue ▸ (by omega : n<B)⟩)
  obtain ⟨σ1,r1,p1⟩ := RamArraySum.command_spec B M "flow.weights" (List.ofFn weights) hB
    (by simp only [List.length_ofFn]; omega)
    (by intro q hq; obtain ⟨v,rfl⟩ := List.mem_ofFn.mp hq; exact num_bound (hw v))
    (by intro q hq; obtain ⟨v,rfl⟩ := List.mem_ofFn.mp hq; exact den_bound (hw v))
    (fun i => num_bound (hs i)) (fun i => den_bound (hs i)) ν
    ⟨by simp [ν],by simpa only [Prefix,ν,arrs_setVar] using hσ.weightsData⟩
  obtain ⟨σ2,r2,p2⟩ := save_spec B "round.total" (total weights)
    ((num_bound hb.totalBound).trans_lt hMB) ((den_bound hb.totalBound).trans_lt hMB) (by decide) σ1 p1.2
  have rprior := rstart.seq (r1.seq r2)
  obtain ⟨σ3,r3,p3⟩ := RamSupport.command_spec B M weights (by omega) hMB (by omega)
    (fun v => num_bound (hw v)) (fun v => den_bound (hw v)) σ2
    ⟨(rprior.frame_var "metric.n" (by decide)).trans hσ.nValue,
      by simpa only [Prefix,rprior.frame_arr "flow.weights" (by decide)] using hσ.weightsData⟩
  obtain ⟨σ4,r4,p4⟩ := RamGridBudget.command_spec B (support weights) hp (by omega) σ3 p3.2.2
  have rafter := r3.seq r4
  have rbefore := rstart.seq (r1.seq (r2.seq (r3.seq r4)))
  have hconstants : RamRoundingConstants.Input cost (total weights) (support weights) σ4 :=
    ⟨RamRoundingConstants.storedFrame rbefore hσ.costData (by decide) (by decide),
      RamRoundingConstants.storedFrame rafter p2 (by decide) (by decide),p4.1,p4.2⟩
  obtain ⟨τ,r5,p5⟩ := RamRoundingConstants.command_spec B M cost (total weights) (support weights) hb hM hB σ4 hconstants
  have rr := rstart.seq (r1.seq (r2.seq (r3.seq (r4.seq r5))))
  refine ⟨τ,rr.mono ?_,?_,p5⟩
  · simp only [List.length_ofFn,RamRoundingConstants.unitCost]
    nlinarith
  · exact ⟨(rr.frame_var _ (by decide)).trans hσ.nValue,
      by simpa only [Prefix,rr.frame_arr "flow.weights" (by decide)] using hσ.weightsData,
      RamRoundingConstants.storedFrame rr hσ.costData (by decide) (by decide)⟩

end Lax455465Proofs.RamRoundingInit
