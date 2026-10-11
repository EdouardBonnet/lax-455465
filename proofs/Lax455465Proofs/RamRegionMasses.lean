import Lax455465Proofs.RamRegionContext
import Lax455465Proofs.RamRegionDirection

namespace Lax455465Proofs.RamRegionMasses

open RegionQueryData RamRegionContext Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamUnsignedScalar RamVirtualState
open scoped NNRat

def command : Com := .seq (RamBallMass.command true)
  (.seq (RamBallMass.command false) RamRegionDirection.command)

set_option maxHeartbeats 1600000 in
/-- Compute both strict balls from runtime distances and residual weights,
then select their smaller mass. All geometric and graph inputs survive. -/
theorem command_spec (B H : ℕ) {n : ℕ} (q : Query n) (hb : RegionQueryHeight.Bounds q H)
    (hB : 2*(2^H)^2+3 < B) (hindex : 2*n+2 < B) :
    Spec B (fun σ => Input q σ ∧ 2*n < (σ.arrs "region.outMask").length ∧ 2*n < (σ.arrs "region.inMask").length)
      command (fun _ τ => Masks q τ ∧
        Stored "region.outMass" (BallMassData.mass q.weights q.outDistance q.radius) τ ∧
        Stored "region.inMass" (BallMassData.mass q.weights q.inDistance q.radius) τ)
      ((144*H+584)*n+130) := by
  have hball (b : Bool) : Spec B (fun σ => Input q σ ∧ 2*n < (σ.arrs (RamBallMass.maskArray b)).length)
      (RamBallMass.command b) (fun _ τ => Input q τ ∧
        Prefix (RamUnsignedBuffer.encode (BallMassData.mask (distance q b) q.radius)) (RamBallMass.maskArray b) τ ∧
        Stored (RamBallMass.massName b) (BallMassData.mass q.weights (distance q b) q.radius) τ)
      ((36*((2^H)^2).size+256)*n+32) := by
    rintro σ ⟨hctx,hroom⟩
    obtain ⟨τ,rr,pr⟩ := RamBallMass.command_spec B (2^H) b q.weights (distance q b) q.radius hB hindex
      (num_bound hb.radiusBound) (den_bound hb.radiusBound)
      (fun v => num_bound (hb.weightsBound v)) (fun v => den_bound (hb.weightsBound v))
      (fun v => num_bound (hb.distanceBound b v)) (fun v => den_bound (hb.distanceBound b v))
      (fun i => num_bound (hb.massPrefixBound b i)) (fun i => den_bound (hb.massPrefixBound b i)) σ ⟨hctx.ballContext b,hroom⟩
    refine ⟨τ,rr,Input.frame rr hctx (by cases b <;> dsimp [sourceVariables] <;> decide)
      (by cases b <;> dsimp [arrays] <;> decide),pr.2⟩
  rintro σ ⟨hctx,hoRoom,hiRoom⟩
  obtain ⟨ν,ro,po⟩ := hball true σ ⟨hctx,hoRoom⟩
  obtain ⟨μ,ri,pi⟩ := hball false ν ⟨po.1,by change 2*n < (ν.arrs "region.inMask").length; rwa [RamFrames.run_array_length ro "region.inMask"]⟩
  have hoMass : Stored "region.outMass" (BallMassData.mass q.weights q.outDistance q.radius) μ := by
    simpa only [distance,RamBallMass.massName,if_true,Stored,String.reduceAppend,ri.frame_var "region.outMass.n" (by decide),
      ri.frame_var "region.outMass.d" (by decide)] using po.2.2
  have hiMass : Stored "region.inMass" (BallMassData.mass q.weights q.inDistance q.radius) μ := pi.2.2
  obtain ⟨τ,rd,pd⟩ := RamRegionDirection.command_spec B (2^H) q.weights q.outDistance q.inDistance q.radius hB
    (num_bound (mass_height q H hb true)) (den_bound (mass_height q H hb true))
    (num_bound (mass_height q H hb false)) (den_bound (mass_height q H hb false)) μ ⟨hoMass,hiMass⟩
  have rr := ro.seq (ri.seq rd)
  refine ⟨τ,rr.mono ?_,⟨Input.frame rr hctx (by dsimp [sourceVariables]; decide) (by dsimp [arrays]; decide),?_,?_,pd.2.2⟩,pd.1,pd.2.1⟩
  · rw [←Nat.pow_mul,Nat.size_pow]
    ring_nf; omega
  · have ra := ri.seq rd
    simpa only [distance,RamBallMass.maskArray,if_true,Prefix,ra.frame_arr "region.outMask" (by decide)] using po.2.1
  · simpa only [distance,RamBallMass.maskArray,Bool.false_eq_true,if_false,Prefix,rd.frame_arr "region.inMask" (by decide)] using pi.2.1

end Lax455465Proofs.RamRegionMasses
