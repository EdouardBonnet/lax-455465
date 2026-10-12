import Lax455465Proofs.RamActiveRemove
import Lax455465Proofs.RamRegionRecord
import Lax455465Proofs.RamRegionQuery

namespace Lax455465Proofs.RamSmallRegion
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamRegionRecord RamRegionContext
open scoped NNRat

def ball {n : ℕ} (distance : Fin n → ℚ≥0) (radius : ℚ≥0) : Finset (Fin n) :=
  RegionCharging.ball (fun v => (distance v : ℚ)) radius

theorem mask_eq {n : ℕ} (distance : Fin n → ℚ≥0) (radius : ℚ≥0) :
    BallMassData.mask distance radius=MaskedMassData.flags (ResidualData.mask (ball distance radius)) := by
  rw [BallMassData.mask_eq]
  congr 1
  funext v
  simp [ResidualData.mask,ball,RegionCharging.ball]

structure Input {n : ℕ} (q : RegionQueryData.Query n) (active : Finset (Fin n))
    (history : List (Entry n)) (root : Fin n) (σ : Env) : Prop where
  masks : Masks q σ
  rootValue : σ.vars "region.root"=root.val
  activeData : Prefix (RamUnsignedBuffer.encode (MaskedMassData.flags (ResidualData.mask active))) "region.active" σ
  historyData : Prefix (words history) "region.history" σ
  historyPosition : σ.vars "history.pos"=4*history.length

structure Room (n len : ℕ) (σ : Env) : Prop where
  historyRoom : 4*len+4≤(σ.arrs "region.history").length
  activeRoom : 2*n≤(σ.arrs "region.active").length
  nextRoom : 2*n<(σ.arrs "region.nextActive").length

def selected {n : ℕ} (q : RegionQueryData.Query n) (root : Fin n) : Entry n :=
  ⟨root,q.radius,RegionQueryData.direction q q.radius⟩
def command : Com := .seq RamRegionRecord.command RamActiveRemove.command

set_option maxHeartbeats 1600000 in
/-- A small-ball iteration records the actual query and removes precisely
its selected oriented ball from the active buffer. -/
theorem command_spec (B : ℕ) {n : ℕ} (q : RegionQueryData.Query n) (active : Finset (Fin n))
    (history : List (Entry n)) (root : Fin n) (hindex : 2*n+2<B) (hlen : 4*history.length+4<B)
    (hnum : q.radius.num<B) (hden : q.radius.den<B)
    (hdo : q.outDistance=q.length root) (hdi : q.inDistance=(fun v => q.length v root)) :
    Spec B (fun σ => Input q active history root σ ∧ Room n history.length σ) command
      (fun _ τ => τ.vars "metric.n"=n ∧
        Prefix (words (history++[selected q root])) "region.history" τ ∧
        τ.vars "history.pos"=4*(history.length+1) ∧
        Prefix (RamUnsignedBuffer.encode (MaskedMassData.flags
          (ResidualData.mask (active \ (selected q root).region.ball (MetricMatrix.rational q.length))))) "region.active" τ)
      (96*n+50) := by
  rintro σ ⟨hσ,hroom⟩
  obtain ⟨ν,rr,pr⟩ := RamRegionRecord.command_spec B history (selected q root) hlen (by omega) hnum hden σ
    ⟨⟨hσ.historyData,by simpa only [length_words] using hσ.historyPosition,hσ.rootValue,
      hσ.masks.input.radiusData,hσ.masks.directionValue⟩,hroom.historyRoom⟩
  have hc : RamActiveRemove.Context active (ball q.outDistance q.radius) (ball q.inDistance q.radius)
      (RegionQueryData.direction q q.radius) ν := by
    refine ⟨(rr.frame_var _ (by decide)).trans hσ.masks.input.nValue,
      (rr.frame_var _ (by decide)).trans hσ.masks.directionValue,?_,?_,?_⟩
    · simpa only [Prefix,rr.frame_arr "region.active" (by decide)] using hσ.activeData
    · simpa only [Prefix,rr.frame_arr "region.outMask" (by decide),mask_eq] using hσ.masks.outMask
    · simpa only [Prefix,rr.frame_arr "region.inMask" (by decide),mask_eq] using hσ.masks.inMask
  obtain ⟨τ,ra,pa⟩ := RamActiveRemove.command_spec B active (ball q.outDistance q.radius) (ball q.inDistance q.radius)
    (RegionQueryData.direction q q.radius) (by omega) hindex ν
    ⟨hc,by rw [RamFrames.run_array_length rr "region.nextActive"]; exact hroom.nextRoom,
      by rw [RamFrames.run_array_length rr "region.active"]; exact hroom.activeRoom⟩
  refine ⟨τ,(rr.seq ra).mono (by omega),pa.1,?_,?_,?_⟩
  · simpa only [Prefix,ra.frame_arr "region.history" (by decide)] using pr.1
  · exact (ra.frame_var _ (by decide)).trans pr.2
  · have hball : (selected q root).region.ball (MetricMatrix.rational q.length)=
        if RegionQueryData.direction q q.radius then ball q.outDistance q.radius else ball q.inDistance q.radius := by
      unfold selected RamRegionRecord.Entry.region RegionLoop.Region.ball ball
      rw [hdo,hdi]
      rfl
    simpa only [RamActiveRemove.removed,hball] using pa.2

end Lax455465Proofs.RamSmallRegion
