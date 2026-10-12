import Lax455465Proofs.SupportData
import Lax455465Proofs.RamUnsignedBuffer
import Lax455465Proofs.RamFrames

namespace Lax455465Proofs.RamSupport
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamRational
open scoped NNRat

def inspect : Com := .seq (RamUnsignedBuffer.read "flow.weights" "support.i")
  (.ite (.eq (.var "rat.n") (.lit 0)) .skip
    (.assign "round.support" (.add (.var "round.support") (.lit 1))))
def step : Com := .seq inspect (.assign "support.i" (.add (.var "support.i") (.lit 1)))
def command : Com := .seq (.assign "round.support" (.lit 0))
  (.seq (.assign "support.i" (.lit 0)) (.while (.lt (.var "support.i") (.var "metric.n")) step))

def Invariant {n : ℕ} (weights : Fin n → ℚ≥0) (σ : Env) : Prop :=
  σ.vars "metric.n"=n ∧ Prefix (RamUnsignedBuffer.encode (List.ofFn weights)) "flow.weights" σ ∧
    σ.vars "support.i"≤n ∧ σ.vars "round.support"=SupportData.count ((List.ofFn weights).take (σ.vars "support.i"))

set_option maxHeartbeats 1200000 in
theorem step_spec (B M : ℕ) {n : ℕ} (weights : Fin n → ℚ≥0) (h2 : 2<B)
    (hM : M<B) (hindex : 2*n+2<B)
    (hn : ∀ v, (weights v).num≤M) (hd : ∀ v, (weights v).den≤M) :
    Spec B (fun σ => Invariant weights σ ∧ σ.vars "support.i"<n) step
      (fun σ τ => Invariant weights τ ∧ τ.vars "support.i"=σ.vars "support.i"+1) 28 := by
  rintro σ ⟨⟨horder,hprefix,hile,hcount⟩,hi⟩
  let i := σ.vars "support.i"
  let qs := List.ofFn weights
  have hqi : i<qs.length := by simpa only [qs,List.length_ofFn] using hi
  have he : qs[i] = weights ⟨i,hi⟩ := by simp only [qs,List.getElem_ofFn]
  have hnB : qs[i].num<B := by rw [he]; exact (hn _).trans_lt hM
  have hdB : qs[i].den<B := by rw [he]; exact (hd _).trans_lt hM
  have hcounter : σ.vars "round.support" ≤ i := by
    rw [hcount]
    exact (SupportData.count_le _).trans (by simp only [List.length_take,List.length_ofFn,Nat.min_eq_left hile]; rfl)
  obtain ⟨ν,rr,pr⟩ := RamUnsignedBuffer.read_spec B "flow.weights" "support.i" qs i hqi h2 (by omega) hnB hdB (by decide) σ ⟨hprefix,rfl⟩
  have hrat : ν.vars "rat.n"=qs[i].num := by simpa only [NNRat.natAbs_num_coe] using pr.1.2.1
  have hcv : ν.vars "round.support"=SupportData.count (qs.take i) :=
    (rr.frame_var "round.support" (by decide)).trans hcount
  have hci : ν.vars "support.i"=i := (rr.frame_var _ (by decide)).trans rfl
  have hc : (Cond.eq (.var "rat.n") (.lit 0)).evalB B ν = some (decide (qs[i].num=0)) := by
    rw [evalB_condEq (evalB_var (hrat ▸ hnB)) (evalB_lit (by omega)),hrat]
    rfl
  have hf : ∃ μ, Run B (.ite (.eq (.var "rat.n") (.lit 0)) .skip
      (.assign "round.support" (.add (.var "round.support") (.lit 1)))) ν μ 8 ∧
      μ.vars "round.support"=SupportData.count (qs.take (i+1)) := by
    by_cases hz : qs[i].num=0
    · refine ⟨ν,(Run.ite_true (d := .assign "round.support" (.add (.var "round.support") (.lit 1)))
        (by simpa only [hz,decide_true] using hc) Run.skip).mono (by dsimp [Cond.size,Expr.size]; omega),?_⟩
      rw [SupportData.count_step qs i hqi]
      simpa only [hz,Nat.lt_irrefl,if_false,Nat.add_zero] using hcv
    · let μ := ν.setVar "round.support" (SupportData.count (qs.take i)+1)
      have hcB : ν.vars "round.support"+1<B := by rw [rr.frame_var "round.support" (by decide)]; omega
      have rc : Run B (.assign "round.support" (.add (.var "round.support") (.lit 1))) ν μ 4 :=
        Run.assign (evalB_bin (op := .add) (by rw [evalB_var_iff]; exact ⟨hcv.symm,by omega⟩)
          (evalB_lit (by omega)) (by dsimp [Bop.apply]; rw [←hcv]; exact hcB))
      refine ⟨μ,(Run.ite_false (c := Com.skip) (by simpa only [hz,decide_false] using hc) rc).mono (by dsimp [Cond.size,Expr.size]; omega),?_⟩
      simp only [μ,vars_setVar,if_true,SupportData.count_step qs i hqi,if_pos (Nat.pos_of_ne_zero hz)]
  obtain ⟨μ,rf,pf⟩ := hf
  have hmi : μ.vars "support.i"=i := (rf.frame_var _ (by decide)).trans hci
  have rinc : Run B (.assign "support.i" (.add (.var "support.i") (.lit 1))) μ (μ.setVar "support.i" (i+1)) 4 :=
    Run.assign (evalB_bin (op := .add) (by rw [evalB_var_iff]; exact ⟨hmi.symm,by rw [hmi]; omega⟩)
      (evalB_lit (by omega)) (by dsimp [Bop.apply]; omega))
  have run := (rr.seq rf).seq rinc
  refine ⟨μ.setVar "support.i" (i+1),run.mono (by omega),?_,by simp [i]⟩
  refine ⟨(run.frame_var _ (by decide)).trans horder,?_,by simp; omega,?_⟩
  · simpa only [Prefix,run.frame_arr "flow.weights" (by decide)] using hprefix
  · simpa only [vars_setVar,String.reduceEq,if_false,if_true] using pf

set_option maxHeartbeats 1200000 in
/-- Count the positive input weights from their actual canonical numerator
words. Zero-weight transit vertices remain in the graph. -/
theorem command_spec (B M : ℕ) {n : ℕ} (weights : Fin n → ℚ≥0) (h2 : 2<B)
    (hM : M<B) (hindex : 2*n+2<B)
    (hn : ∀ v, (weights v).num≤M) (hd : ∀ v, (weights v).den≤M) :
    Spec B (fun σ => σ.vars "metric.n"=n ∧ Prefix (RamUnsignedBuffer.encode (List.ofFn weights)) "flow.weights" σ)
      command (fun _ τ => τ.vars "metric.n"=n ∧ Prefix (RamUnsignedBuffer.encode (List.ofFn weights)) "flow.weights" τ ∧
        τ.vars "round.support"=(RegionSelection.support (fun v => (weights v : ℚ))).card)
      (32*n+8) := by
  have hloop := Spec.forRangeZero "support.i" "metric.n" (Invariant weights) n 28 (by omega)
    (fun _ h => h.2.2.1) (fun _ h => h.1) (step_spec B M weights h2 hM hindex hn hd)
  rintro σ ⟨horder,hprefix⟩
  let ν := σ.setVar "round.support" 0
  have rzero : Run B (.assign "round.support" (.lit 0)) σ ν 2 := Run.assign (evalB_lit (by omega))
  have hinit : Invariant weights (ν.setVar "support.i" 0) := by
    refine ⟨by simpa only [ν,vars_setVar,String.reduceEq,if_false] using horder,
      by simpa only [Prefix,ν,arrs_setVar] using hprefix,by simp,?_⟩
    simp [ν,SupportData.count]
  obtain ⟨τ,rr,pr⟩ := hloop ν hinit
  refine ⟨τ,(rzero.seq rr).mono (by omega),pr.1.1,pr.1.2.1,?_⟩
  have ht : (List.ofFn weights).take n=List.ofFn weights := by simp
  simpa only [pr.2,ht,SupportData.count_support] using pr.1.2.2.2

end Lax455465Proofs.RamSupport
