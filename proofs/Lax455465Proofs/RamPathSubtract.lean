import Lax455465Proofs.LayeredPathSweep
import Lax455465Proofs.RamResidualUpdate

namespace Lax455465Proofs.RamPathSubtract
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState
open LayeredFlowLP RamPathState RamPathEdgeRead LayeredPathSweep
open scoped NNRat

def step : Com := .seq RamPathEdgeRead.command
  (.seq RamResidualUpdate.command (.assign "short.level" (.add (.var "short.level") (.lit 1))))

def command : Com := .seq (.assign "short.level" (.lit 0))
  (.while (.lt (.var "short.level") (.var "short.layer")) step)

def Invariant {n L : ℕ} (q : Coordinate n L → ℚ≥0) (w : ℚ≥0) (st : Edge n)
    (path : Fin (L+1) → Fin n) (σ : Env) : Prop :=
  σ.vars "short.level"≤L ∧ Context (after q w st path (σ.vars "short.level")) st path σ ∧
    RamUnsignedScalar.Stored "short.amount" w σ

theorem step_spec (B M : ℕ) {n L : ℕ} (q : Coordinate n L → ℚ≥0) (w : ℚ≥0)
    (st : Edge n) (path : Fin (L+1) → Fin n) (hB : 2*M^2+3<B)
    (hsize : n+n*n+L*(n*n)+2*(1+(n*n)*(L*(n*n)))+2*L+20<B)
    (hnum : ∀ i≤L,∀ j,(after q w st path i j).num≤M)
    (hden : ∀ i≤L,∀ j,(after q w st path i j).den≤M) (hwn : w.num≤M) (hwd : w.den≤M) :
    Spec B (fun σ => Invariant q w st path σ ∧ σ.vars "short.level"<L) step
      (fun σ τ => Invariant q w st path τ ∧ τ.vars "short.level"=σ.vars "short.level"+1)
      (36*(M^2).size+252) := by
  have hMB : M<B := by nlinarith only [hB]
  rintro σ ⟨⟨hle,hcontext,hw⟩,hlt⟩
  let k : Fin L := ⟨σ.vars "short.level",hlt⟩
  let qk := after q w st path k.val
  let j := edge st path k
  obtain ⟨ν,r1,p1⟩ := RamPathEdgeRead.index_spec B qk st path k hsize
    (fun j => (hnum k.val hle j).trans_lt hMB) (fun j => (hden k.val hle j).trans_lt hMB) σ ⟨hcontext,rfl⟩
  have hwν : RamUnsignedScalar.Stored "short.amount" w ν := by
    simpa only [RamUnsignedScalar.Stored,String.reduceAppend,r1.frame_var "short.amount.n" (by decide),
      r1.frame_var "short.amount.d" (by decide)] using hw
  have hidx : ν.vars "short.arcIndex"=j.val := p1.2.2
  have hcurrent : qk j=q j := current q w st path k
  have hnext : Function.update qk j (RamTruncatedSubtract.value (qk j) w)=after q w st path (k.val+1) := by
    rw [hcurrent]
    exact (after_succ q w st path k).symm
  have hnewnum : (RamTruncatedSubtract.value (qk j) w).num<B := by
    have hh := hnum (k.val+1) (by omega) j
    rw [←hnext,Function.update_self] at hh
    exact hh.trans_lt hMB
  have hnewden : (RamTruncatedSubtract.value (qk j) w).den<B := by
    have hh := hden (k.val+1) (by omega) j
    rw [←hnext,Function.update_self] at hh
    exact hh.trans_lt hMB
  obtain ⟨μ,r2,p2⟩ := RamResidualUpdate.command_spec B M qk j w hB (by omega)
    (hnum k.val hle j) (hden k.val hle j) hwn hwd hnewnum hnewden ν
    ⟨UnsignedArray.of_prefix qk "flow.primal" ν p1.1.1.buffer,hidx,hwν⟩
  have hpnew : Prefix (RamUnsignedBuffer.encode (List.ofFn (after q w st path (k.val+1)))) "flow.primal" μ := by
    simpa only [hnext] using UnsignedArray.to_prefix _ "flow.primal" μ p2
  have hdμ := replace_data r2 p1.1.1 (by decide) hpnew
  have hrawμ : Prefix (List.ofFn fun i => (path i).val) "short.raw" μ := by
    simpa only [Prefix,r2.frame_arr "short.raw" (by decide)] using p1.1.2
  have hwμ : RamUnsignedScalar.Stored "short.amount" w μ := by
    simpa only [RamUnsignedScalar.Stored,String.reduceAppend,r2.frame_var "short.amount.n" (by decide),
      r2.frame_var "short.amount.d" (by decide)] using hwν
  have hlevelμ : μ.vars "short.level"=k.val := ((r1.seq r2).frame_var "short.level" (by decide)).trans rfl
  let τ := μ.setVar "short.level" (k.val+1)
  have r3 : Run B (.assign "short.level" (.add (.var "short.level") (.lit 1))) μ τ 4 :=
    Run.assign (evalB_bin (op := .add)
      (by rw [evalB_var_iff]; exact ⟨hlevelμ.symm,hlevelμ ▸ (by omega : k.val<B)⟩)
      (evalB_lit (by omega)) (by dsimp [Bop.apply]; omega))
  refine ⟨τ,(r1.seq (r2.seq r3)).mono (by omega),?_,by simp [τ,k]⟩
  refine ⟨by simp [τ] <;> omega,?_,?_⟩
  · have hdτ := data_frame r3 hdμ (by decide) (by decide)
    simpa only [Context,Prefix,τ,vars_setVar,if_true,arrs_setVar] using And.intro hdτ hrawμ
  · simpa only [RamUnsignedScalar.Stored,τ,vars_setVar,String.reduceAppend,String.reduceEq,if_false] using hwμ

/-- The complete in-place sweep computes precisely the simultaneous path
subtraction, because layer-indexed coordinates are distinct. -/
theorem command_spec (B M : ℕ) {n L : ℕ} (q : Coordinate n L → ℚ≥0) (w : ℚ≥0)
    (st : Edge n) (path : Fin (L+1) → Fin n) (hB : 2*M^2+3<B)
    (hsize : n+n*n+L*(n*n)+2*(1+(n*n)*(L*(n*n)))+2*L+20<B)
    (hnum : ∀ i≤L,∀ j,(after q w st path i j).num≤M)
    (hden : ∀ i≤L,∀ j,(after q w st path i j).den≤M) (hwn : w.num≤M) (hwd : w.den≤M) :
    Spec B (fun σ => Context q st path σ ∧ RamUnsignedScalar.Stored "short.amount" w σ) command
      (fun _ τ => Context (after q w st path L) st path τ ∧ RamUnsignedScalar.Stored "short.amount" w τ)
      ((36*(M^2).size+256)*L+6) := by
  have hscan := Spec.forRangeZero "short.level" "short.layer" (Invariant q w st path) L
    (36*(M^2).size+252) (by omega) (fun _ h => h.1) (fun _ h => h.2.1.1.layer)
    (step_spec B M q w st path hB hsize hnum hden hwn hwd)
  rintro σ ⟨hctx,hw⟩
  have hinit : Invariant q w st path (σ.setVar "short.level" 0) := by
    refine ⟨by simp,?_,?_⟩
    · simpa only [Context,Prefix,vars_setVar,if_true,after_zero,arrs_setVar] using
        And.intro (RamPathState.set_var hctx.1 "short.level" 0 (by decide)) hctx.2
    · simpa only [RamUnsignedScalar.Stored,vars_setVar,String.reduceAppend,String.reduceEq,if_false] using hw
  obtain ⟨τ,rr,pr⟩ := hscan σ hinit
  exact ⟨τ,rr.mono (by ring_nf; omega),by simpa only [pr.2] using pr.1.2.1,pr.1.2.2⟩

end Lax455465Proofs.RamPathSubtract
