import Lax455465Proofs.RamRegionScan

set_option maxRecDepth 8192
namespace Lax455465Proofs.RamRegionBoundedLoop
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRegionInvariant RegionRuntimeState RamRegionState
open Lax455465.RationalEncoding
open scoped NNRat

def initial (n : ℕ) : State n := ⟨Finset.univ,[],.running⟩
def cost (n p M H : ℕ) : ℕ := (RamRegionCore.cost n p M H+13)*(p+1)+6

set_option maxHeartbeats 4800000 in
/-- The fixed native region loop executes all its iterations with one bound
and returns the exact final deterministic state. Its only data are the graph,
metric and constants already computed in native buffers. -/
theorem command_spec (B M H : ℕ) {n : ℕ} (I : RationalInstance n) (length : MetricMatrix.Matrix n)
    (seed beta delta threshold : ℚ≥0) (p : ℕ)
    (hM : 1≤M) (hk : RegionBudget.steps p≤M) (hB : 2*M^2+3<B) (hquery : 2*(2^H)^2+3<B)
    (hindex : 2*(n*n)+2<B) (hvertex : 2*n+2<B) (hradius : 2*(RegionBudget.steps p+1+2*n)+2<B)
    (hlen : 4*p+4<B) (ht : LpInputSize.Height (2^H) (threshold : ℚ))
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
    (hsupport : (RegionSelection.support (RegionLoop.weights I Finset.univ)).card≤p) :
    Spec B (fun σ => Fixed I length seed beta delta threshold p σ ∧ Room n p σ ∧
      σ.vars "loop.limit"=p+1 ∧ View I length seed beta (initial n) σ)
      RamRegionScan.command (fun _ τ => Fixed I length seed beta delta threshold p τ ∧ Room n p τ ∧
        View I length seed beta ((advance I length seed beta delta threshold p)^[p+1] (initial n)) τ)
      (cost n p M H) := by
  apply RamRegionScan.command_spec B (RamRegionCore.cost n p M H) I length seed beta delta threshold p (initial n)
    (by nlinarith) (by omega) hbeta hdiag
  · simpa only [RegionRuntimeProgress.SupportBound,initial,List.length_nil,Nat.zero_add] using hsupport
  · intro s hbound _
    have hhist : s.history.length≤p := by unfold RegionRuntimeProgress.SupportBound at hbound; omega
    exact RamRegionCore.iteration_spec B M H I length seed beta delta threshold p s.active s.history hM hk hB hquery
      hindex hvertex hradius (by omega) ht hwn hwd hcn hcd hl hd hu (hb s.active) hbeta hseed hdelta hp htri hcost hhist

end Lax455465Proofs.RamRegionBoundedLoop
