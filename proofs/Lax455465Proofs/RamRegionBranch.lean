import Lax455465Proofs.RamSmallRegion
import Lax455465Proofs.RamRegionLarge

namespace Lax455465Proofs.RamRegionBranch
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar
open RegionQueryData RamRegionRecord
open scoped NNRat

def large {n : ℕ} (q : Query n) (threshold : ℚ≥0) : Prop :=
  (threshold : ℚ)≤BallMassData.mass q.weights q.outDistance q.radius ∧
    (threshold : ℚ)≤BallMassData.mass q.weights q.inDistance q.radius
instance {n : ℕ} (q : Query n) (threshold : ℚ≥0) : Decidable (large q threshold) := inferInstanceAs (Decidable (_∧_))

def branch : Com := .ite (.eq (.var "region.large") (.lit 1))
  (.assign "region.phase" (.lit 1)) RamSmallRegion.command

def command : Com := .seq RamRegionLarge.command branch

structure Input {n : ℕ} (q : Query n) (threshold : ℚ≥0) (active : Finset (Fin n))
    (history : List (Entry n)) (root : Fin n) (σ : Env) : Prop where
  smallInput : RamSmallRegion.Input q active history root σ
  phase : σ.vars "region.phase"=0
  thresholdData : Stored "round.largeThreshold" threshold σ
  outMass : Stored "region.outMass" (BallMassData.mass q.weights q.outDistance q.radius) σ
  inMass : Stored "region.inMass" (BallMassData.mass q.weights q.inDistance q.radius) σ

def Output {n : ℕ} (q : Query n) (threshold : ℚ≥0) (active : Finset (Fin n))
    (history : List (Entry n)) (root : Fin n) (σ : Env) : Prop :=
  if large q threshold then
    σ.vars "region.phase"=1 ∧ RamSmallRegion.Input q active history root σ
  else
    σ.vars "region.phase"=0 ∧ σ.vars "metric.n"=n ∧
      Prefix (words (history++[RamSmallRegion.selected q root])) "region.history" σ ∧
      σ.vars "history.pos"=4*(history.length+1) ∧
      Prefix (RamUnsignedBuffer.encode (MaskedMassData.flags (ResidualData.mask
        (active \ (RamSmallRegion.selected q root).region.ball (MetricMatrix.rational q.length))))) "region.active" σ

set_option maxHeartbeats 2400000 in
/-- The runtime large-ball test either freezes the actual selected query or
records and removes its small ball. This implements the branch of the
mathematical region loop without an externally supplied decision bit. -/
theorem command_spec (B H : ℕ) {n : ℕ} (q : Query n) (threshold : ℚ≥0) (active : Finset (Fin n))
    (history : List (Entry n)) (root : Fin n) (hb : RegionQueryHeight.Bounds q H)
    (hB : 2*(2^H)^2+3<B) (ht : LpInputSize.Height (2^H) (threshold : ℚ))
    (hindex : 2*n+2<B) (hlen : 4*history.length+4<B)
    (hdo : q.outDistance=q.length root) (hdi : q.inDistance=(fun v => q.length v root)) :
    Spec B (fun σ => Input q threshold active history root σ ∧ RamSmallRegion.Room n history.length σ)
      command (fun _ τ => Output q threshold active history root τ) (96*n+188) := by
  have h2 : 2<B := by nlinarith [(Nat.one_le_two_pow : 1≤2^H)]
  have hHB : 2^H<B := by nlinarith [(Nat.one_le_two_pow : 1≤2^H)]
  rintro σ ⟨hσ,hroom⟩
  obtain ⟨ν,rl,pl⟩ := RamRegionLarge.command_spec B (2^H) threshold
    (BallMassData.mass q.weights q.outDistance q.radius) (BallMassData.mass q.weights q.inDistance q.radius)
    hB ht (RamRegionContext.mass_height q H hb true) (RamRegionContext.mass_height q H hb false) σ
    ⟨hσ.thresholdData,hσ.outMass,hσ.inMass⟩
  have hi : RamSmallRegion.Input q active history root ν := by
    have hm := hσ.smallInput.masks
    refine ⟨⟨RamRegionContext.Input.frame rl hm.input (by dsimp [RamRegionContext.sourceVariables]; decide)
      (by dsimp [RamRegionContext.arrays]; decide),?_,?_,?_⟩,
      (rl.frame_var _ (by decide)).trans hσ.smallInput.rootValue,?_,?_,
      (rl.frame_var _ (by decide)).trans hσ.smallInput.historyPosition⟩
    · simpa only [Prefix,rl.frame_arr "region.outMask" (by decide)] using hm.outMask
    · simpa only [Prefix,rl.frame_arr "region.inMask" (by decide)] using hm.inMask
    · exact (rl.frame_var _ (by decide)).trans hm.directionValue
    · simpa only [Prefix,rl.frame_arr "region.active" (by decide)] using hσ.smallInput.activeData
    · simpa only [Prefix,rl.frame_arr "region.history" (by decide)] using hσ.smallInput.historyData
  have hf : ν.vars "region.large"=if large q threshold then 1 else 0 := pl.2
  by_cases hl : large q threshold
  · have hc : (Cond.eq (.var "region.large") (.lit 1)).evalB B ν=some true := by
      have he : ν.vars "region.large"=1 := by simpa only [hl,if_true] using hf
      rw [evalB_condEq (evalB_var (he ▸ (by omega : 1<B))) (evalB_lit (by omega)),he]
      rfl
    let τ := ν.setVar "region.phase" 1
    have rp : Run B (.assign "region.phase" (.lit 1)) ν τ 2 := Run.assign (evalB_lit (by omega))
    refine ⟨τ,(rl.seq (Run.ite_true (d := RamSmallRegion.command) hc rp)).mono (by dsimp [Cond.size,Expr.size]; omega),?_⟩
    simp only [Output,hl,if_true]
    refine ⟨by simp [τ],?_⟩
    have hm := hi.masks
    exact ⟨⟨RamRegionContext.Input.frame rp hm.input (by dsimp [RamRegionContext.sourceVariables]; decide)
      (by dsimp [RamRegionContext.arrays]; decide),
      by simpa only [Prefix,τ,arrs_setVar] using hm.outMask,
      by simpa only [Prefix,τ,arrs_setVar] using hm.inMask,
      by simpa only [τ,vars_setVar,String.reduceEq,if_false] using hm.directionValue⟩,
      (rp.frame_var _ (by decide)).trans hi.rootValue,
      by simpa only [Prefix,τ,arrs_setVar] using hi.activeData,
      by simpa only [Prefix,τ,arrs_setVar] using hi.historyData,
      (rp.frame_var _ (by decide)).trans hi.historyPosition⟩
  · have hc : (Cond.eq (.var "region.large") (.lit 1)).evalB B ν=some false := by
      have he : ν.vars "region.large"=0 := by simpa only [hl,if_false] using hf
      rw [evalB_condEq (evalB_var (he ▸ (by omega : 0<B))) (evalB_lit (by omega)),he]
      rfl
    obtain ⟨τ,rs,ps⟩ := RamSmallRegion.command_spec B q active history root hindex hlen
      ((RamRegionContext.num_bound hb.radiusBound).trans_lt hHB)
      ((RamRegionContext.den_bound hb.radiusBound).trans_lt hHB) hdo hdi ν
      ⟨hi,⟨by rw [RamFrames.run_array_length rl "region.history"]; exact hroom.historyRoom,
        by rw [RamFrames.run_array_length rl "region.active"]; exact hroom.activeRoom,
        by rw [RamFrames.run_array_length rl "region.nextActive"]; exact hroom.nextRoom⟩⟩
    have rr := rl.seq (Run.ite_false (c := .assign "region.phase" (.lit 1)) hc rs)
    refine ⟨τ,rr.mono (by dsimp [Cond.size,Expr.size]; omega),?_⟩
    simp only [Output,hl,if_false]
    exact ⟨((rl.seq rs).frame_var _ (by decide)).trans hσ.phase,ps⟩

end Lax455465Proofs.RamRegionBranch
