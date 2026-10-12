import Lax455465Proofs.RamRegionChoice
import Lax455465Proofs.RamRegionBranch

set_option maxRecDepth 4096
namespace Lax455465Proofs.RamRegionIteration
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar RamRegionSetup
open RegionQueryData RamRegionRecord
open scoped NNRat

def command : Com := .seq RamRegionSetup.command RamRegionBranch.command

structure State {n : ℕ} (active : Finset (Fin n)) (history : List (Entry n))
    (threshold : ℚ≥0) (σ : Env) : Prop where
  phase : σ.vars "region.phase"=0
  thresholdData : Stored "round.largeThreshold" threshold σ
  activeData : Prefix (RamUnsignedBuffer.encode (MaskedMassData.flags (ResidualData.mask active))) "region.active" σ
  historyData : Prefix (words history) "region.history" σ
  historyPosition : σ.vars "history.pos"=4*history.length

set_option maxHeartbeats 3200000 in
/-- A complete selected-root iteration performs the native candidate search,
then takes exactly the large-ball or small-ball branch of the region loop. -/
theorem command_spec (B M H : ℕ) {n : ℕ} (weights : Fin n → ℚ≥0)
    (capacity length : MetricMatrix.Matrix n) (root : Fin n) (seed beta delta threshold : ℚ≥0) (p : ℕ)
    (active : Finset (Fin n)) (history : List (Entry n))
    (hk : RegionBudget.steps p≤M) (hB : 2*M^2+3<B) (hquery : 2*(2^H)^2+3<B)
    (hindex : 2*(n*n)+2<B) (hvertex : 2*n+2<B) (hradius : 2*(RegionBudget.steps p+1+2*n)+2<B)
    (hlen : 4*history.length+4<B) (ht : LpInputSize.Height (2^H) (threshold : ℚ))
    (hl : ∀ u v, LpInputSize.Height M (length u v : ℚ))
    (hd : LpInputSize.Height M (delta : ℚ))
    (hu : LpInputSize.Height M ((delta/(RegionBudget.steps p : ℚ≥0) : ℚ≥0) : ℚ))
    (hb : ∀ i, ∀ hi : i<(RadiusData.candidates (length root) (fun v => length v root) (RegionBudget.steps p) delta).length,
      RegionQueryHeight.Bounds (RadiusSearchData.atRadius (query weights capacity length root seed beta)
        (RadiusData.candidates (length root) (fun v => length v root) (RegionBudget.steps p) delta)[i]) H)
    (hbeta : (beta : ℚ)=RegionSearch.slope (RegionBudget.steps p) delta)
    (r : ℚ) (hs : RegionSearch.search (MetricMatrix.rational capacity) (MetricMatrix.rational length)
      (fun v => (length root v : ℚ)) (fun v => (length v root : ℚ)) seed delta p
      (RegionSelection.direction (fun v => (weights v : ℚ)) (fun v => (length root v : ℚ))
        (fun v => (length v root : ℚ)))=some r) :
    Spec B (fun σ => Input weights capacity length root seed beta delta (RegionBudget.steps p) σ ∧
      State active history threshold σ ∧ Room n (RegionBudget.steps p+1+2*n) σ ∧ RamSmallRegion.Room n history.length σ)
      command (fun _ τ => ∃ rn : ℚ≥0, (rn : ℚ)=r ∧
        RamRegionBranch.Output (RadiusSearchData.atRadius (query weights capacity length root seed beta) rn)
          threshold active history root τ)
      (RamRegionSetup.cost n (RegionBudget.steps p) M H+96*n+188) := by
  rintro σ ⟨hσ,hstate,hroom,hsmallRoom⟩
  obtain ⟨ν,rs,rn,hr,hm,_,pa⟩ := RamRegionChoice.command_spec B M H weights capacity length root seed beta delta p
    hk hB hquery hindex hvertex hradius hl hd hu hb hbeta r hs σ ⟨hσ,hroom⟩
  have hbounds : RegionQueryHeight.Bounds (RadiusSearchData.atRadius (query weights capacity length root seed beta) rn) H := by
    obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hm
    subst rn
    exact hb i hi
  have hinput : RamRegionBranch.Input (RadiusSearchData.atRadius (query weights capacity length root seed beta) rn)
      threshold active history root ν := by
    refine ⟨⟨pa.1,(rs.frame_var _ (by decide)).trans hσ.rootValue,?_,?_,
      (rs.frame_var _ (by decide)).trans hstate.historyPosition⟩,
      (rs.frame_var _ (by decide)).trans hstate.phase,
      RamRoundingConstants.storedFrame rs hstate.thresholdData (by decide) (by decide),pa.2.1,pa.2.2.1⟩
    · simpa only [Prefix,rs.frame_arr "region.active" (by decide)] using hstate.activeData
    · simpa only [Prefix,rs.frame_arr "region.history" (by decide)] using hstate.historyData
  obtain ⟨τ,rb,pb⟩ := RamRegionBranch.command_spec B H (RadiusSearchData.atRadius (query weights capacity length root seed beta) rn)
    threshold active history root hbounds hquery ht hvertex hlen rfl rfl ν
    ⟨hinput,⟨by rw [RamFrames.run_array_length rs "region.history"]; exact hsmallRoom.historyRoom,
      by rw [RamFrames.run_array_length rs "region.active"]; exact hsmallRoom.activeRoom,
      by rw [RamFrames.run_array_length rs "region.nextActive"]; exact hsmallRoom.nextRoom⟩⟩
  exact ⟨τ,(rs.seq rb).mono (by omega),rn,hr,pb⟩

end Lax455465Proofs.RamRegionIteration
