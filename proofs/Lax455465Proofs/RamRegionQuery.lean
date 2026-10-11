import Lax455465Proofs.RamRegionMasses
import Lax455465Proofs.RamRegionMeasures
import Lax455465Proofs.RamRegionAcceptance

set_option maxRecDepth 4096

namespace Lax455465Proofs.RamRegionQuery

open RegionQueryData RamRegionContext Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamUnsignedScalar RamVirtualState
open scoped NNRat

def command : Com := .seq RamRegionMasses.command (.seq RamRegionMeasures.command RamRegionAcceptance.command)

set_option maxHeartbeats 1600000 in
/-- One fixed native query computes both balls and their masses, chooses the
orientation, evaluates its boundary and seeded volume, and returns exactly
the candidate-radius predicate searched by deterministic region growth. -/
theorem command_spec (B H : ℕ) {n : ℕ} (q : Query n) (hb : RegionQueryHeight.Bounds q H)
    (hB : 2*(2^H)^2+3 < B) (hindex : 2*(n*n)+2 < B) (hvertex : 2*n+2 < B) :
    Spec B (fun σ => Input q σ ∧ 2*n < (σ.arrs "region.outMask").length ∧
      2*n < (σ.arrs "region.inMask").length ∧ 2*(n*n) < (σ.arrs "region.crossing").length)
      command (fun _ τ => Masks q τ ∧
        Stored "region.outMass" (BallMassData.mass q.weights q.outDistance q.radius) τ ∧
        Stored "region.inMass" (BallMassData.mass q.weights q.inDistance q.radius) τ ∧
        Stored "region.boundary" (boundary q) τ ∧ Stored "region.volume" (volume q) τ ∧
        Stored "query.bound" (bound q) τ ∧ τ.vars "find.ok" = if accepted q then 1 else 0)
      ((288*H+880)*(n*n)+(144*H+584)*n+144*H+554) := by
  rintro σ ⟨hctx,hoRoom,hiRoom,hcRoom⟩
  obtain ⟨ν,rm,pm⟩ := RamRegionMasses.command_spec B H q hb hB hvertex σ ⟨hctx,hoRoom,hiRoom⟩
  obtain ⟨μ,rv,pv⟩ := RamRegionMeasures.command_spec B H q hb hB hindex hvertex ν
    ⟨pm.1,by rwa [RamFrames.run_array_length rm "region.crossing"]⟩
  obtain ⟨τ,ra,pa⟩ := RamRegionAcceptance.command_spec B H q hb hB μ pv
  have rr := rm.seq (rv.seq ra)
  refine ⟨τ,rr.mono (by ring_nf; omega),pa.1,?_,?_,?_,?_,pa.2⟩
  · have rafter := rv.seq ra
    simpa only [Stored,String.reduceAppend,rafter.frame_var "region.outMass.n" (by decide),rafter.frame_var "region.outMass.d" (by decide)] using pm.2.1
  · have rafter := rv.seq ra
    simpa only [Stored,String.reduceAppend,rafter.frame_var "region.inMass.n" (by decide),rafter.frame_var "region.inMass.d" (by decide)] using pm.2.2
  · simpa only [Stored,String.reduceAppend,ra.frame_var "region.boundary.n" (by decide),ra.frame_var "region.boundary.d" (by decide)] using pv.2.1
  · simpa only [Stored,String.reduceAppend,ra.frame_var "region.volume.n" (by decide),ra.frame_var "region.volume.d" (by decide)] using pv.2.2

end Lax455465Proofs.RamRegionQuery
