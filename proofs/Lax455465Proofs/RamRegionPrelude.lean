import Lax455465Proofs.RamRegionInvariant
import Lax455465Proofs.RamRoot

namespace Lax455465Proofs.RamRegionPrelude
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamRegionInvariant RamRegionRecord
open Lax455465.RationalEncoding
open scoped NNRat

def command : Com := .seq RamResidual.command RamRoot.command

def cost (n M : ℕ) : ℕ := (36*(M^2).size+208)*(n*n)+(36*(M^2).size+166)*n+40

set_option maxHeartbeats 2400000 in
/-- Rebuild the current residual graph and find its first positive root,
while preserving the original graph, metric, constants and region history. -/
theorem command_spec (B M : ℕ) {n : ℕ} (I : RationalInstance n) (length : MetricMatrix.Matrix n)
    (seed beta delta threshold : ℚ≥0) (p : ℕ) (active : Finset (Fin n)) (history : List (Entry n))
    (hM : 1≤M) (hB : 2*M^2+3<B) (hindex : 2*(n*n)+2<B) (hvertex : 2*n+2<B)
    (hwn : ∀ v, (I.weight v).num≤M) (hwd : ∀ v, (I.weight v).den≤M)
    (hcn : ∀ u v, (I.capacity u v).num≤M) (hcd : ∀ u v, (I.capacity u v).den≤M) :
    Spec B (fun σ => Fixed I length seed beta delta threshold p σ ∧ Dynamic active history σ ∧ Room n p σ)
      command (fun _ τ => Fixed I length seed beta delta threshold p τ ∧ Dynamic active history τ ∧ Room n p τ ∧
        Prefix (RamUnsignedBuffer.encode (MetricMatrix.values (ResidualData.capacity I active))) "region.capacities" τ ∧
        Prefix (RamUnsignedBuffer.encode (List.ofFn (ResidualData.weights I active))) "region.weights" τ ∧
        RamFind.Matches ((RegionSelection.chooseRoot (RegionLoop.weights I active)).map Fin.val) τ)
      (cost n M) := by
  have hMB : M<B := by nlinarith
  rintro σ ⟨hσ,hd,hr⟩
  obtain ⟨ν,rr,pr⟩ := RamResidual.command_spec B M I active hM hB hindex hvertex hwn hwd hcn hcd σ
    ⟨⟨hσ.nValue,hσ.n2Value,hσ.weightsData,hσ.capacityData,hd.activeData⟩,
      by simpa only [Nat.mul_assoc] using hr "region.arcActive" (2*n*n) (by simp [extents]),
      by simpa only [Nat.mul_assoc] using hr "region.capacities" (2*n*n) (by simp [extents]),
      hr "region.weights" (2*n) (by simp [extents])⟩
  have hnum : ∀ v, (ResidualData.weights I active v).num≤M := by
    intro v
    unfold ResidualData.weights
    split_ifs
    · exact hwn v
    · simp
  have hden : ∀ v, (ResidualData.weights I active v).den≤M := by
    intro v
    unfold ResidualData.weights
    split_ifs
    · exact hwd v
    · simpa using hM
  obtain ⟨τ,rf,pf⟩ := RamRoot.command_spec B M (ResidualData.weights I active) (by nlinarith) hMB hvertex hnum hden ν
    ⟨pr.1.1,pr.2.2⟩
  have run := rr.seq rf
  refine ⟨τ,run.mono (by dsimp [cost]; nlinarith),
    Fixed.frame run hσ (by dsimp [names]; decide) (by dsimp [arrays]; decide),
    Dynamic.frame run hd (by dsimp [dynamicNames]; decide) (by dsimp [dynamicArrays]; decide),Room.frame run hr,?_,pf.1.2.2,?_⟩
  · simpa only [Prefix,rf.frame_arr "region.capacities" (by decide)] using pr.2.1
  · simpa only [ResidualData.rational_weights] using pf.2

end Lax455465Proofs.RamRegionPrelude
