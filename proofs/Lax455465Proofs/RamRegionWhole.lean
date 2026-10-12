import Lax455465Proofs.RamRegionBegin
import Lax455465Proofs.RegionRuntimeCorrespondence

set_option maxRecDepth 8192
namespace Lax455465Proofs.RamRegionWhole
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRegionInvariant RegionRuntimeState RamRegionState
open Lax455465.RationalEncoding
open scoped NNRat

theorem combine {B KI KS : ℕ} {σ ν τ : Env}
    (hi : Run B RamRegionBegin.command σ ν KI) (hs : Run B RamRegionScan.command ν τ KS) :
    Run B RamRegionLoop.command σ τ (KI+KS) := by
  obtain ⟨ki,hki,hbi⟩ := hi
  obtain ⟨ks,hks,hbs⟩ := hs
  cases hbi with
  | seq ht haSetup =>
    cases haSetup with
    | seq ha hsetup =>
      cases hsetup with
      | seq hpos hphaseLimit =>
        cases hphaseLimit with
        | seq hphase hlimit =>
          exact ⟨_,by omega,.seq ht (.seq ha (.seq hpos (.seq hphase (.seq hlimit hbs))))⟩

set_option maxHeartbeats 4800000 in
theorem command_spec (B M H : ℕ) {n : ℕ} (I : RationalInstance n) (length : MetricMatrix.Matrix n)
    (seed beta delta : ℚ≥0) (p : ℕ)
    (hM : 3≤M) (hk : RegionBudget.steps p≤M) (hB : 2*M^2+3<B) (hquery : 2*(2^H)^2+3<B)
    (hindex : 2*(n*n)+2<B) (hvertex : 2*n+2<B) (hradius : 2*(RegionBudget.steps p+1+2*n)+2<B)
    (hlen : 4*p+4<B) (hthreshold : LpInputSize.Height (2^H) (RamLargeThreshold.threshold (RamRoundingInit.total I.weight) : ℚ))
    (hwn : ∀ v, (I.weight v).num≤M) (hwd : ∀ v, (I.weight v).den≤M)
    (hcn : ∀ u v, (I.capacity u v).num≤M) (hcd : ∀ u v, (I.capacity u v).den≤M)
    (hl : ∀ u v, LpInputSize.Height M (length u v : ℚ))
    (hd : LpInputSize.Height M (delta : ℚ))
    (hu : LpInputSize.Height M ((delta/(RegionBudget.steps p : ℚ≥0) : ℚ≥0) : ℚ))
    (hb : ∀ active : Finset (Fin n), ∀ root : Fin n, ∀ i,
      ∀ hi : i<(RadiusData.candidates (length root) (fun v => length v root) (RegionBudget.steps p) delta).length,
      RegionQueryHeight.Bounds (RadiusSearchData.atRadius (RegionExecutionData.query I length active root seed beta)
        (RadiusData.candidates (length root) (fun v => length v root) (RegionBudget.steps p) delta)[i]) H)
    (hbeta : (beta : ℚ)=RegionSearch.slope (RegionBudget.steps p) delta)
    (hseed : 0<(seed : ℚ)) (hdelta : 0<(delta : ℚ)) (hp : 0<p)
    (hdiag : ∀ v, length v v=0)
    (htri : ∀ u v w, (length u w : ℚ)≤(length u v : ℚ)+(length v w : ℚ))
    (hcost : RegionRounding.metricCost I (MetricMatrix.rational length)≤(p : ℚ)*(seed : ℚ))
    (hsupport : (RegionSelection.support (RegionLoop.weights I Finset.univ)).card≤p)
    (htotal : LpInputSize.Height M (RamRoundingInit.total I.weight : ℚ)) :
    Spec B (fun σ => RamRegionBegin.Source I length seed beta delta p σ ∧ Room n p σ) RamRegionLoop.command
      (fun _ τ => Fixed I length seed beta delta (RamLargeThreshold.threshold (RamRoundingInit.total I.weight)) p τ ∧ Room n p τ ∧
        View I length seed beta ((advance I length seed beta delta (RamLargeThreshold.threshold (RamRoundingInit.total I.weight)) p)^[p+1]
          (RamRegionBoundedLoop.initial n)) τ ∧
        RegionRuntimeCorrespondence.ValidFinal I length seed delta p
          ((advance I length seed beta delta (RamLargeThreshold.threshold (RamRoundingInit.total I.weight)) p)^[p+1]
            (RamRegionBoundedLoop.initial n)))
      (36*((RamRoundingInit.total I.weight).den*3).size+28*n+112+RamRegionBoundedLoop.cost n p M H) := by
  rintro σ ⟨hσ,hroom⟩
  obtain ⟨ν,rb,pb⟩ := RamRegionBegin.command_spec B M I length seed beta delta p hM hB htotal hvertex (by omega) σ ⟨hσ,hroom⟩
  obtain ⟨τ,rs,ps⟩ := RamRegionBoundedLoop.command_spec B M H I length seed beta delta
    (RamLargeThreshold.threshold (RamRoundingInit.total I.weight)) p (by omega) hk hB hquery hindex hvertex hradius hlen
    hthreshold hwn hwd hcn hcd hl hd hu hb hbeta hseed hdelta hp hdiag htri hcost hsupport ν pb
  exact ⟨τ,combine rb rs,ps.1,ps.2.1,ps.2.2,
    RegionRuntimeCorrespondence.final_correct I length seed beta delta p hbeta hseed hdelta hp hdiag htri hcost hsupport⟩

end Lax455465Proofs.RamRegionWhole
