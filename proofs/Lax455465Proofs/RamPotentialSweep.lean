import Lax455465Proofs.RamThresholdCandidate
import Lax455465Proofs.RamBestFold

set_option maxRecDepth 8192
namespace Lax455465Proofs.RamPotentialSweep
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar RamRegionContext
open Lax455465.RationalEncoding RamThresholdCandidate
open scoped NNRat

def restore : Com := .seq (.assign "cut.candidate" (.var "best.index")) RamThresholdCandidate.command
def finish : Com := .ite (.eq (.var "best.found") (.lit 1)) restore .skip
def command : Com := .seq (RamBestFold.command RamThresholdCandidate.command) finish
def cost (n M : ℕ) : ℕ := (RamThresholdCandidate.cost n M+92)*n+RamThresholdCandidate.cost n M+16

def Selected {n : ℕ} (reversed : Bool) (potential : Fin n → ℚ≥0) : Option ℕ → Env → Prop
  | none, _ => True
  | some j, σ => Prefix (RamUnsignedBuffer.encode
      (CutScoreData.vertexFlags (ThresholdCutData.candidate reversed potential j))) "cut.flags" σ

theorem input_set {n : ℕ} {I : RationalInstance n} {potential : Fin n → ℚ≥0} {reversed : Bool}
    (σ : Env) (k : ℕ) (name : String) (hn : name∈["cut.candidate","best.found","best.index"])
    (h : Input I potential reversed σ) : Input I potential reversed (σ.setVar name k) := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hn
  rcases hn with rfl | rfl | rfl
  all_goals
    exact ⟨by simpa using h.nValue,by simpa using h.n2Value,by simpa using h.count,
      by simpa using h.reversedValue,by simpa [Stored] using h.totalData,
      h.weightsData,h.capacityData,h.potentialData,h.maskRoom,h.crossingRoom⟩

set_option maxHeartbeats 4800000 in
/-- The complete native sweep evaluates every vertex threshold, retains an
admissible minimum-ratio candidate, and restores its actual vertex mask. -/
theorem command_spec (B M : ℕ) {n : ℕ} (I : RationalInstance n) (potential : Fin n → ℚ≥0) (reversed : Bool)
    (hM : 1≤M) (hB : 2*M^2+3<B) (hindex : 2*(n*n)+2<B) (hvertex : 2*n+2<B)
    (hp : ∀ v,LpInputSize.Height M (potential v : ℚ))
    (hb : ∀ i<n,CutScoreHeight.Bounds I (ThresholdCutData.candidate reversed potential i) M) :
    Spec B (Input I potential reversed) command
      (fun _ τ => Input I potential reversed τ ∧
        RamBestUpdate.Matches (ThresholdCutData.score I reversed potential)
          (BestCutIndex.best (ThresholdCutData.valid I reversed potential) (ThresholdCutData.score I reversed potential) n) τ ∧
        Selected reversed potential
          (BestCutIndex.best (ThresholdCutData.valid I reversed potential) (ThresholdCutData.score I reversed potential) n) τ)
      (cost n M) := by
  let valid := ThresholdCutData.valid I reversed potential
  let value := ThresholdCutData.score I reversed potential
  let best := BestCutIndex.best valid value n
  have producer (i : ℕ) (hi : i<n) := RamThresholdCandidate.command_spec B M I potential reversed i hi hM hB hindex hvertex hp (hb i hi)
  have scan := RamBestFold.command_spec B M (RamThresholdCandidate.cost n M) (Input I potential reversed)
    valid value n RamThresholdCandidate.command hB (by omega)
    (fun i hi => (hb i hi).ratioBound) (fun _ h => h.count) input_set
    (fun i hi σ h => by obtain ⟨τ,rr,pr⟩ := producer i hi σ h; exact ⟨τ,rr,pr.1,pr.2.1⟩)
    (by dsimp [RamBestFold.bestNames]; decide)
    (fun rr h => Input.frame rr h (by dsimp [RamThresholdCandidate.names]; decide) (by dsimp [RamThresholdCandidate.arrays]; decide))
  rintro σ hσ
  obtain ⟨ν,rs,ps⟩ := scan σ hσ
  change Input I potential reversed ν ∧ RamBestUpdate.Matches value best ν at ps
  have h1 : 1<B := by nlinarith
  have hf : ∃ τ,Run B finish ν τ (RamThresholdCandidate.cost n M+6) ∧
      Input I potential reversed τ ∧ RamBestUpdate.Matches value best τ ∧ Selected reversed potential best τ := by
    cases he : best with
    | none =>
      have hv : ν.vars "best.found"=0 := by simpa only [he,RamBestUpdate.Matches] using ps.2
      have hc : (Cond.eq (.var "best.found") (.lit 1)).evalB B ν=some false := by
        rw [evalB_condEq (evalB_var (hv ▸ (by omega : 0<B))) (evalB_lit h1),hv]
        rfl
      exact ⟨ν,(Run.ite_false (c := restore) hc Run.skip).mono (by dsimp [Cond.size,Expr.size]; omega),
        ps.1,hv,trivial⟩
    | some j =>
      have hj : j<n := (BestCutIndex.best_sound valid value n j he).1
      have hm : RamBestUpdate.Matches value (some j) ν := by simpa only [he] using ps.2
      have hc : (Cond.eq (.var "best.found") (.lit 1)).evalB B ν=some true := by
        rw [evalB_condEq (evalB_var (hm.1 ▸ h1)) (evalB_lit h1),hm.1]
        rfl
      let μ := ν.setVar "cut.candidate" j
      have ri : Run B (.assign "cut.candidate" (.var "best.index")) ν μ 2 :=
        Run.assign (by rw [evalB_var_iff]; exact ⟨hm.2.1.symm,by rw [hm.2.1]; omega⟩)
      obtain ⟨τ,rp,pp⟩ := producer j hj μ ⟨input_set ν j "cut.candidate" (by simp) ps.1,by simp [μ]⟩
      have rr := Run.ite_true (d := .skip) hc (ri.seq rp)
      exact ⟨τ,rr.mono (by dsimp [Cond.size,Expr.size]; omega),pp.1,
        RamBestFold.Matches.frame rr hm (by dsimp [RamBestFold.bestNames]; decide),pp.2.2⟩
  obtain ⟨τ,rf,pf⟩ := hf
  exact ⟨τ,(rs.seq rf).mono (by dsimp [cost]; omega),pf⟩

/-- Any admissible shore furnished by the mathematical sweep bounds the
actual native winner. This transfers rounding bounds without assuming an
externally supplied optimal threshold. -/
theorem selected_le {n : ℕ} (I : RationalInstance n) (potential : Fin n → ℚ≥0) (reversed : Bool)
    (S : Finset (Fin n)) (hS : S∈CutSweeps.candidates (ThresholdCutData.potential reversed potential))
    (hvalid : CutSweeps.admissibleQ I S) :
    ∃ j, BestCutIndex.best (ThresholdCutData.valid I reversed potential)
        (ThresholdCutData.score I reversed potential) n=some j ∧ j<n ∧
      CutSweeps.admissibleQ I (ThresholdCutData.candidate reversed potential j) ∧
      CutSweeps.ratioQ I (ThresholdCutData.candidate reversed potential j)≤CutSweeps.ratioQ I S := by
  rw [←ThresholdCutData.candidates_eq] at hS
  obtain ⟨k,hk,hget⟩ := List.mem_iff_getElem.mp hS
  have hkn : k<n := by simpa only [ThresholdCutData.length_candidates] using hk
  have hcan : ThresholdCutData.candidate reversed potential k=S := by
    rw [ThresholdCutData.candidate,List.getD_eq_get _ ∅ ⟨k,hk⟩]
    exact hget
  have hv : ThresholdCutData.valid I reversed potential k := by
    simpa only [ThresholdCutData.valid,hcan] using hvalid
  cases he : BestCutIndex.best (ThresholdCutData.valid I reversed potential)
      (ThresholdCutData.score I reversed potential) n with
  | none => exact False.elim ((BestCutIndex.best_none _ _ _).mp he k hkn hv)
  | some j =>
    have hs := BestCutIndex.best_sound _ _ n j he
    refine ⟨j,rfl,hs.1,hs.2,?_⟩
    have hm := BestCutIndex.best_minimal _ _ n j k he hkn hv
    have hq := NNRat.coe_le_coe.mpr hm
    simpa only [ThresholdCutData.score,CutScoreData.coe_ratio,hcan] using hq

end Lax455465Proofs.RamPotentialSweep
