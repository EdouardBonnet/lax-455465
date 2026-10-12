import Lax455465Proofs.RamRegionCut
import Lax455465Proofs.RegionRuntimeBounds

set_option maxRecDepth 8192
namespace Lax455465Proofs.RamPositiveRounding
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamUnsignedScalar RamRegionInvariant RegionRuntimeState
open Lax455465.RationalEncoding
open scoped NNRat

def command : Com := .seq RamRegionLoop.command RamRegionCut.command

set_option maxHeartbeats 6400000 in
/-- Run region growth from the original graph and metric, then dispatch on
its actual terminal state and construct a cut satisfying the uniform bound. -/
theorem command_spec (B M H N : ℕ) {n : ℕ} (I : RationalInstance n) (length : MetricMatrix.Matrix n)
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
    (htotal : LpInputSize.Height M (RamRoundingInit.total I.weight : ℚ))
    (hN : 1 ≤ N) (hMN : M*M ≤ N) (hpN : 2*p ≤ N) (hNB : 2*N^2+3 < B)
    (hlargeBounds : ∀ Tin Tout : Finset (Fin n),∀ hin : Tin.Nonempty,∀ hout : Tout.Nonempty,
      LargePotentialData.Bounds I length Tin Tout hin hout N)
    (hcuts : ∀ S,CutScoreHeight.Bounds I S N)
    (htotalPos : 0 < LargeBallRounding.total I)
    (hsep : 1 ≤ LargeBallRounding.distanceSeparation I (MetricMatrix.rational length))
    (hseedEq : (seed : ℚ)=RegionRounding.metricCost I (MetricMatrix.rational length)/p)
    (hdeltaEq : (delta : ℚ)=RegionRounding.radiusBudget I) :
    Spec B (fun σ => RamRegionBegin.Source I length seed beta delta p σ ∧ Room n p σ ∧ RamRegionCut.Room n σ)
      command (fun _ τ => RamRegionCut.Output I length p τ)
      (36*((RamRoundingInit.total I.weight).den*3).size+28*n+112+
        RamRegionBoundedLoop.cost n p M H+RamRegionCut.cost n p N) := by
  rintro σ ⟨hσ,hregionRoom,hcutRoom⟩
  obtain ⟨ν,rr,pr⟩ := RamRegionWhole.command_spec B M H I length seed beta delta p hM hk hB hquery hindex hvertex
    hradius hlen hthreshold hwn hwd hcn hcd hl hd hu hb hbeta hseed hdelta hp hdiag htri hcost hsupport htotal σ ⟨hσ,hregionRoom⟩
  let s := (advance I length seed beta delta (RamLargeThreshold.threshold (RamRoundingInit.total I.weight)) p)^[p+1]
    (RamRegionBoundedLoop.initial n)
  have hh := RegionRuntimeBounds.iterate_height I length seed beta delta
    (RamLargeThreshold.threshold (RamRoundingInit.total I.weight)) p M (p+1) (by omega) hk hl hd hu
  have hMN' : M ≤ N := by nlinarith
  have htotalν := RamRoundingConstants.storedFrame rr hσ.totalData (by decide) (by decide)
  obtain ⟨τ,rc,pc⟩ := RamRegionCut.command_spec B N I length seed beta delta
    (RamLargeThreshold.threshold (RamRoundingInit.total I.weight)) p s hN hpN hNB (by nlinarith) hlen hindex hvertex
    (fun u v => LpInputSize.height_mono (hl u v) hMN')
    (fun e he => LpInputSize.height_mono (hh e he) hMN)
    hlargeBounds hcuts htotalPos hp hdiag hsep htri hseedEq hdeltaEq pr.2.2.2 ν
    ⟨pr.1,pr.2.2.1,htotalν,hcutRoom.frame rr⟩
  exact ⟨τ,rr.seq rc,pc⟩

end Lax455465Proofs.RamPositiveRounding
