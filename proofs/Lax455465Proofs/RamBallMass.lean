import Lax455465Proofs.BallMassData
import Lax455465Proofs.RamRootDistances

namespace Lax455465Proofs.RamBallMass

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamVirtualState RamUnsignedScalar
open scoped NNRat

def maskArray (outward : Bool) : String := if outward then "region.outMask" else "region.inMask"
def massName (outward : Bool) : String := if outward then "region.outMass" else "region.inMass"

def Context {n : ℕ} (outward : Bool) (weights distance : Fin n → ℚ≥0) (radius : ℚ≥0) (σ : Env) : Prop :=
  σ.vars "metric.n" = n ∧ Stored "region.radius" radius σ ∧
    Prefix (RamUnsignedBuffer.encode (List.ofFn weights)) "region.weights" σ ∧
    Prefix (RamUnsignedBuffer.encode (List.ofFn distance)) (RamRootDistances.array outward) σ

def command (outward : Bool) : Com := .seq (.assign "ball.count" (.var "metric.n"))
  (.seq (RamBallMask.command (RamRootDistances.array outward) (maskArray outward))
    (.seq (.assign "sum.count" (.var "ball.count"))
      (.seq (RamMaskedSum.command "region.weights" (maskArray outward)) (save (massName outward)))))

set_option maxHeartbeats 1600000 in
/-- Compute a strict ball and its exact residual mass from initialized
runtime vectors. The returned mask is retained for boundary and removal
commands, and its mass agrees with the region-selection expression. -/
theorem command_spec (B M : ℕ) {n : ℕ} (outward : Bool) (weights distance : Fin n → ℚ≥0) (radius : ℚ≥0)
    (hB : 2*M^2+3 < B) (hindex : 2*n+2 < B)
    (hrn : radius.num ≤ M) (hrd : radius.den ≤ M)
    (hwn : ∀ v, (weights v).num ≤ M) (hwd : ∀ v, (weights v).den ≤ M)
    (hdn : ∀ v, (distance v).num ≤ M) (hdd : ∀ v, (distance v).den ≤ M)
    (hprefixNum : ∀ i, ((RamMaskedSum.coefficients (List.ofFn weights) (BallMassData.mask distance radius)).take i).sum.num ≤ M)
    (hprefixDen : ∀ i, ((RamMaskedSum.coefficients (List.ofFn weights) (BallMassData.mask distance radius)).take i).sum.den ≤ M) :
    Spec B (fun σ => Context outward weights distance radius σ ∧ 2*n < (σ.arrs (maskArray outward)).length)
      (command outward) (fun _ τ => Context outward weights distance radius τ ∧
        Prefix (RamUnsignedBuffer.encode (BallMassData.mask distance radius)) (maskArray outward) τ ∧
        Stored (massName outward) (BallMassData.mass weights distance radius) τ)
      ((36*(M^2).size+256)*n+32) := by
  have hM : M < B := by nlinarith
  have hM1 : 1 ≤ M := radius.den_pos.trans_le hrd
  let qs := List.ofFn weights
  let ds := List.ofFn distance
  let ms := BallMassData.mask distance radius
  have hqLen : qs.length = n := List.length_ofFn
  have hdLen : ds.length = n := List.length_ofFn
  have hmLen : ms.length = n := by simp [ms,BallMassData.mask]
  have hwN : ∀ q ∈ qs, q.num ≤ M := by
    intro q hq
    obtain ⟨v,rfl⟩ := List.mem_ofFn.mp hq
    exact hwn v
  have hwD : ∀ q ∈ qs, q.den ≤ M := by
    intro q hq
    obtain ⟨v,rfl⟩ := List.mem_ofFn.mp hq
    exact hwd v
  have hdN : ∀ q ∈ ds, q.num ≤ M := by
    intro q hq
    obtain ⟨v,rfl⟩ := List.mem_ofFn.mp hq
    exact hdn v
  have hdD : ∀ q ∈ ds, q.den ≤ M := by
    intro q hq
    obtain ⟨v,rfl⟩ := List.mem_ofFn.mp hq
    exact hdd v
  have hmN : ∀ q ∈ ms, q.num ≤ M := by
    intro q hq
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hq
    unfold RamBallMask.flag
    split_ifs <;> norm_num <;> omega
  have hmD : ∀ q ∈ ms, q.den ≤ M := by
    intro q hq
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hq
    unfold RamBallMask.flag
    split_ifs <;> norm_num <;> omega
  have hfinal : (BallMassData.mass weights distance radius).num ≤ M ∧
      (BallMassData.mass weights distance radius).den ≤ M := by
    simpa only [BallMassData.mass,List.take_length] using
      And.intro (hprefixNum (RamMaskedSum.coefficients (List.ofFn weights) (BallMassData.mask distance radius)).length)
        (hprefixDen (RamMaskedSum.coefficients (List.ofFn weights) (BallMassData.mask distance radius)).length)
  rintro σ ⟨hctx,hroom⟩
  let ρ := σ.setVar "ball.count" n
  have rstart : Run B (.assign "ball.count" (.var "metric.n")) σ ρ 2 :=
    Run.assign (by rw [evalB_var_iff]; exact ⟨hctx.1.symm,hctx.1 ▸ (by omega : n < B)⟩)
  have hmaskCtx : RamBallMask.Context (RamRootDistances.array outward) ds radius ρ := by
    refine ⟨by simp [ρ,hdLen],?_,?_⟩
    · simpa only [Stored,ρ,vars_setVar,String.reduceEq,if_false,String.reduceAppend] using hctx.2.1
    · simpa only [ds,Prefix,ρ,arrs_setVar] using hctx.2.2.2
  obtain ⟨ν,rmask,pmask⟩ := RamBallMask.command_spec B M (RamRootDistances.array outward) (maskArray outward) ds radius
    (by cases outward <;> decide) hB (by rwa [hdLen]) hrn hrd hdN hdD ρ
    ⟨hmaskCtx,by simpa only [ρ,arrs_setVar,hdLen] using hroom⟩
  have hνcount : ν.vars "ball.count" = n := by simpa only [hdLen] using pmask.1.1
  let ξ := ν.setVar "sum.count" n
  have rcount : Run B (.assign "sum.count" (.var "ball.count")) ν ξ 2 :=
    Run.assign (by rw [evalB_var_iff]; exact ⟨hνcount.symm,hνcount ▸ (by omega : n < B)⟩)
  have hsumCtx : RamMaskedSum.Context "region.weights" (maskArray outward) qs ms ξ := by
    refine ⟨by simp [ξ,hqLen],?_,?_⟩
    · have rr := rstart.seq rmask
      simpa only [Prefix,ξ,arrs_setVar,qs,rr.frame_arr "region.weights" (by cases outward <;> decide)] using hctx.2.2.1
    · simpa only [Prefix,ξ,arrs_setVar,ms,BallMassData.mask,ds] using pmask.2
  obtain ⟨μ,rsum,psum⟩ := RamMaskedSum.command_spec B M "region.weights" (maskArray outward) qs ms
    (by omega) hB (by rwa [hqLen]) hwN hwD hmN hmD hprefixNum hprefixDen ξ hsumCtx
  obtain ⟨τ,rsave,psave⟩ := save_spec B (massName outward) (BallMassData.mass weights distance radius)
    (hfinal.1.trans_lt hM) (hfinal.2.trans_lt hM) (by cases outward <;> decide) μ psum.2
  have rr := rstart.seq (rmask.seq (rcount.seq (rsum.seq rsave)))
  refine ⟨τ,rr.mono ?_,?_,?_,psave⟩
  · simp only [hdLen,hqLen,Nat.add_assoc,Nat.reduceAdd]
    ring_nf
    omega
  · simpa only [Context,Stored,Prefix,String.reduceAppend,
      rr.frame_var "metric.n" (by cases outward <;> decide),
      rr.frame_var "region.radius.n" (by cases outward <;> decide),
      rr.frame_var "region.radius.d" (by cases outward <;> decide),
      rr.frame_arr "region.weights" (by cases outward <;> decide),
      rr.frame_arr (RamRootDistances.array outward) (by cases outward <;> decide)] using hctx
  · have rafter := rcount.seq (rsum.seq rsave)
    simpa only [Prefix,ms,BallMassData.mask,ds,
      rafter.frame_arr (maskArray outward) (by cases outward <;> decide)] using pmask.2

end Lax455465Proofs.RamBallMass
