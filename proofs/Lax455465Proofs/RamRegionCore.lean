import Lax455465Proofs.RamRegionPrelude
import Lax455465Proofs.RamRegionLoop
import Lax455465Proofs.RegionExecutionData

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
namespace Lax455465Proofs.RamRegionCore
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar
open RamRegionInvariant RamRegionRecord Lax455465.RationalEncoding
open scoped NNRat

def Output {n : ℕ} (I : RationalInstance n) (length : MetricMatrix.Matrix n)
    (seed beta delta threshold : ℚ≥0) (p : ℕ) (active : Finset (Fin n)) (history : List (Entry n)) (σ : Env) : Prop :=
  match RegionSelection.chooseRoot (RegionLoop.weights I active) with
  | none => σ.vars "region.phase"=2 ∧
      Prefix (words history) "region.history" σ ∧ σ.vars "history.pos"=4*history.length ∧
      Prefix (RamUnsignedBuffer.encode (MaskedMassData.flags (ResidualData.mask active))) "region.active" σ
  | some root => ∃ rn : ℚ≥0,
      RegionSearch.search (RegionLoop.capacity I active) (MetricMatrix.rational length)
        (fun v => (length root v : ℚ)) (fun v => (length v root : ℚ)) seed delta p
        (RegionLoop.chooseDirection I (MetricMatrix.rational length) active root)=some (rn : ℚ) ∧
      RamRegionBranch.Output (RadiusSearchData.atRadius (RegionExecutionData.query I length active root seed beta) rn)
        threshold active history root σ

def cost (n p M H : ℕ) : ℕ := RamRegionPrelude.cost n M+
  RamRegionSetup.cost n (RegionBudget.steps p) M H+96*n+200

set_option maxHeartbeats 4800000 in
/-- One complete native residual iteration agrees with the mathematical
region loop. Search success follows from the stored graph's triangle and
volume-growth hypotheses, with no root or radius supplied by an oracle. -/
theorem iteration_spec (B M H : ℕ) {n : ℕ} (I : RationalInstance n) (length : MetricMatrix.Matrix n)
    (seed beta delta threshold : ℚ≥0) (p : ℕ) (active : Finset (Fin n)) (history : List (Entry n))
    (hM : 1≤M) (hk : RegionBudget.steps p≤M) (hB : 2*M^2+3<B) (hquery : 2*(2^H)^2+3<B)
    (hindex : 2*(n*n)+2<B) (hvertex : 2*n+2<B) (hradius : 2*(RegionBudget.steps p+1+2*n)+2<B)
    (hlen : 4*history.length+4<B) (ht : LpInputSize.Height (2^H) (threshold : ℚ))
    (hwn : ∀ v, (I.weight v).num≤M) (hwd : ∀ v, (I.weight v).den≤M)
    (hcn : ∀ u v, (I.capacity u v).num≤M) (hcd : ∀ u v, (I.capacity u v).den≤M)
    (hl : ∀ u v, LpInputSize.Height M (length u v : ℚ))
    (hd : LpInputSize.Height M (delta : ℚ))
    (hu : LpInputSize.Height M ((delta/(RegionBudget.steps p : ℚ≥0) : ℚ≥0) : ℚ))
    (hb : ∀ root : Fin n, ∀ i, ∀ hi : i<(RadiusData.candidates (length root) (fun v => length v root) (RegionBudget.steps p) delta).length,
      RegionQueryHeight.Bounds (RadiusSearchData.atRadius (RegionExecutionData.query I length active root seed beta)
        (RadiusData.candidates (length root) (fun v => length v root) (RegionBudget.steps p) delta)[i]) H)
    (hbeta : (beta : ℚ)=RegionSearch.slope (RegionBudget.steps p) delta)
    (hseed : 0<(seed : ℚ)) (hdelta : 0<(delta : ℚ)) (hp : 0<p)
    (htri : ∀ u v w, (length u w : ℚ)≤(length u v : ℚ)+(length v w : ℚ))
    (hcost : RegionRounding.metricCost I (MetricMatrix.rational length)≤(p : ℚ)*(seed : ℚ))
    (hHist : history.length≤p) :
    Spec B (fun σ => Fixed I length seed beta delta threshold p σ ∧ Dynamic active history σ ∧ Room n p σ)
      RamRegionLoop.iteration (fun _ τ => Fixed I length seed beta delta threshold p τ ∧ Room n p τ ∧
        Output I length seed beta delta threshold p active history τ) (cost n p M H) := by
  have h2 : 2<B := by nlinarith
  rintro σ ⟨hσ,hstate,hroom⟩
  obtain ⟨σ1,rpre,ppre⟩ := RamRegionPrelude.command_spec B M I length seed beta delta threshold p active history
    hM hB hindex hvertex hwn hwd hcn hcd σ ⟨hσ,hstate,hroom⟩
  have hf := ppre.1
  have hs := ppre.2.1
  have hr := ppre.2.2.1
  have hm := ppre.2.2.2.2.2
  cases hroot : RegionSelection.chooseRoot (RegionLoop.weights I active) with
  | none =>
    have hfound : σ1.vars "find.found"=0 := by simpa only [hroot,Option.map_none,RamFind.Matches] using hm
    have hc : (Cond.eq (.var "find.found") (.lit 1)).evalB B σ1=some false := by
      rw [evalB_condEq (evalB_var (hfound ▸ (by omega : 0<B))) (evalB_lit (by omega)),hfound]
      rfl
    let τ := σ1.setVar "region.phase" 2
    have ra : Run B (.assign "region.phase" (.lit 2)) σ1 τ 2 := Run.assign (evalB_lit h2)
    have rb := Run.ite_false (c := RamRegionLoop.foundRoot) hc ra
    have rr := rpre.seq rb
    have rrun : Run B RamRegionLoop.iteration σ τ (RamRegionPrelude.cost n M+(1+(Cond.eq (.var "find.found") (.lit 1)).size+2)) := by
      simpa only [RamRegionLoop.iteration,RamRegionPrelude.command] using rr
    refine ⟨τ,rrun.mono (by dsimp [cost,Cond.size,Expr.size]; omega),
      Fixed.frame ra hf (by dsimp [names]; decide) (by dsimp [arrays]; decide),Room.frame ra hr,?_⟩
    simp only [Output,hroot]
    exact ⟨by simp [τ],by simpa only [Prefix,τ,arrs_setVar] using hs.historyData,
      (ra.frame_var _ (by decide)).trans hs.historyPosition,
      by simpa only [Prefix,τ,arrs_setVar] using hs.activeData⟩
  | some root =>
    have hfound : σ1.vars "find.found"=1 ∧ σ1.vars "find.result"=root.val := by
      simpa only [hroot,Option.map_some,RamFind.Matches] using hm
    have hc : (Cond.eq (.var "find.found") (.lit 1)).evalB B σ1=some true := by
      rw [evalB_condEq (evalB_var (hfound.1 ▸ (by omega : 1<B))) (evalB_lit (by omega)),hfound.1]
      rfl
    let σ2 := σ1.setVar "region.root" root.val
    have rroot : Run B (.assign "region.root" (.var "find.result")) σ1 σ2 2 :=
      Run.assign (by rw [evalB_var_iff]; exact ⟨hfound.2.symm,hfound.2 ▸ root.isLt.trans (by omega : n<B)⟩)
    have h2f := Fixed.frame rroot hf (by dsimp [names]; decide) (by dsimp [arrays]; decide)
    have h2s := Dynamic.frame rroot hs (by dsimp [dynamicNames]; decide) (by dsimp [dynamicArrays]; decide)
    have h2r := Room.frame rroot hr
    have hsetup : RamRegionSetup.Input (ResidualData.weights I active) (ResidualData.capacity I active)
        length root seed beta delta (RegionBudget.steps p) σ2 :=
      ⟨h2f.nValue,h2f.n2Value,by simp [σ2],h2f.stepsValue,h2f.seedData,h2f.betaData,h2f.deltaData,h2f.unitData,
        by simpa only [Prefix,σ2,arrs_setVar] using ppre.2.2.2.2.1,
        by simpa only [Prefix,σ2,arrs_setVar] using ppre.2.2.2.1,h2f.lengthData⟩
    have hsetupRoom : RamRegionSetup.Room n (RegionBudget.steps p+1+2*n) σ2 :=
      ⟨h2r _ _ (by simp [extents]),h2r _ _ (by simp [extents]),h2r _ _ (by simp [extents]),
        h2r _ _ (by simp [extents]),h2r _ _ (by simp [extents]),
        by simpa only [Nat.mul_assoc] using h2r "region.crossing" (2*n*n) (by simp [extents])⟩
    obtain ⟨r,hsearch⟩ := RegionExecutionData.search_exists I length active root seed delta p hseed hdelta hp htri hcost
    have hsearch' : RegionSearch.search (MetricMatrix.rational (ResidualData.capacity I active)) (MetricMatrix.rational length)
        (fun v => (length root v : ℚ)) (fun v => (length v root : ℚ)) seed delta p
        (RegionSelection.direction (fun v => (ResidualData.weights I active v : ℚ))
          (fun v => (length root v : ℚ)) (fun v => (length v root : ℚ)))=some r := by
      simp only [ResidualData.rational_capacity,ResidualData.rational_weights]
      dsimp only [RegionLoop.chooseDirection,MetricMatrix.rational] at hsearch ⊢
      exact hsearch
    obtain ⟨σ3,rsearch,rn,heq,hmem,hyes,pa⟩ := RamRegionChoice.command_spec B M H
      (ResidualData.weights I active) (ResidualData.capacity I active) length root seed beta delta p
      hk hB hquery hindex hvertex hradius hl hd hu (hb root) hbeta r hsearch' σ2 ⟨hsetup,hsetupRoom⟩
    have h3f := Fixed.frame rsearch h2f (by dsimp [names]; decide) (by dsimp [arrays]; decide)
    have h3s := Dynamic.frame rsearch h2s (by dsimp [dynamicNames]; decide) (by dsimp [dynamicArrays]; decide)
    have h3r := Room.frame rsearch h2r
    let q := RadiusSearchData.atRadius (RegionExecutionData.query I length active root seed beta) rn
    have hbounds : RegionQueryHeight.Bounds q H := by
      obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hmem
      subst rn
      exact hb root i hi
    have hbranch : RamRegionBranch.Input q threshold active history root σ3 :=
      ⟨⟨pa.1,(rsearch.frame_var _ (by decide)).trans hsetup.rootValue,h3s.activeData,h3s.historyData,h3s.historyPosition⟩,
        h3s.phase,h3f.thresholdData,pa.2.1,pa.2.2.1⟩
    have hsmallRoom : RamSmallRegion.Room n history.length σ3 :=
      ⟨(by have hh := h3r "region.history" (4*p+4) (by simp [extents]); omega),
        (h3r "region.active" (2*n) (by simp [extents])).le,h3r "region.nextActive" (2*n) (by simp [extents])⟩
    obtain ⟨τ,rbranch,pbranch⟩ := RamRegionBranch.command_spec B H q threshold active history root hbounds hquery ht hvertex hlen rfl rfl σ3
      ⟨hbranch,hsmallRoom⟩
    have hqueryTest : (Cond.eq (.var "find.found") (.lit 1)).evalB B σ3=some true := by
      rw [evalB_condEq (evalB_var (hyes ▸ (by omega : 1<B))) (evalB_lit (by omega)),hyes]
      rfl
    have rfound := rroot.seq (rsearch.seq (Run.ite_true (d := .assign "region.phase" (.lit 3)) hqueryTest rbranch))
    have rr := rpre.seq (Run.ite_true (d := .assign "region.phase" (.lit 2)) hc rfound)
    change Run B RamRegionLoop.iteration σ τ _ at rr
    refine ⟨τ,rr.mono (by dsimp [cost,Cond.size,Expr.size]; omega),
      Fixed.frame rbranch h3f (by dsimp [names]; decide) (by dsimp [arrays]; decide),Room.frame rbranch h3r,?_⟩
    simp only [Output,hroot]
    exact ⟨rn,by rw [heq]; exact hsearch,pbranch⟩

end Lax455465Proofs.RamRegionCore
