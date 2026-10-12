import Lax455465Proofs.RamBestUpdate

namespace Lax455465Proofs.RamBestFold
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamBestUpdate
open scoped NNRat

def bestNames : List String := ["best.found","best.index","best.value.n","best.value.d"]

theorem Matches.frame {B K : ℕ} {cmd : Com} {σ τ : Env} (rr : Run B cmd σ τ K)
    {value : ℕ → ℚ≥0} {old : Option ℕ} (h : Matches value old σ)
    (hx : ∀ x∈bestNames,x∉cmd.wvars) : Matches value old τ := by
  cases old with
  | none => exact (rr.frame_var _ (hx _ (by simp [bestNames]))).trans h
  | some j =>
    exact ⟨(rr.frame_var _ (hx _ (by simp [bestNames]))).trans h.1,
      (rr.frame_var _ (hx _ (by simp [bestNames]))).trans h.2.1,
      RamRoundingConstants.storedFrame rr h.2.2 (hx _ (by simp [bestNames])) (hx _ (by simp [bestNames]))⟩

def step (producer : Com) : Com := .seq producer (.seq RamBestUpdate.command
  (.assign "cut.candidate" (.add (.var "cut.candidate") (.lit 1))))
def scan (producer : Com) : Com := .seq (.assign "cut.candidate" (.lit 0))
  (.while (.lt (.var "cut.candidate") (.var "cut.count")) (step producer))
def command (producer : Com) : Com := .seq (.assign "best.found" (.lit 0))
  (.seq (.assign "best.index" (.lit 0)) (scan producer))

def Invariant (R : Env → Prop) (valid : ℕ → Prop) [DecidablePred valid] (value : ℕ → ℚ≥0) (count : ℕ) (σ : Env) : Prop :=
  R σ ∧ σ.vars "cut.candidate"≤count ∧ Matches value (BestCutIndex.best valid value (σ.vars "cut.candidate")) σ

set_option maxHeartbeats 4800000 in
/-- A fixed producer is evaluated once per candidate. The native fold stores
exactly the first admissible minimum-ratio index; neither its score nor its
admissibility bit is supplied externally. -/
theorem command_spec (B M K : ℕ) (R : Env → Prop) (valid : ℕ → Prop) [DecidablePred valid]
    (value : ℕ → ℚ≥0) (count : ℕ) (producer : Com) (hB : 2*M^2+3<B) (hcount : count<B)
    (hvalue : ∀ i<count,LpInputSize.Height M (value i : ℚ))
    (hlimit : ∀ σ,R σ→σ.vars "cut.count"=count)
    (hset : ∀ σ k name, name∈["cut.candidate","best.found","best.index"] → R σ→R (σ.setVar name k))
    (hproducer : ∀ i<count,Spec B (fun σ => R σ ∧ σ.vars "cut.candidate"=i) producer
      (fun _ τ => R τ ∧ Current valid value i τ) K)
    (hproducerFrame : ∀ x∈bestNames,x∉producer.wvars)
    (hupdateFrame : ∀ {σ τ : Env} {k : ℕ},Run B RamBestUpdate.command σ τ k→R σ→R τ) :
    Spec B R (command producer) (fun _ τ => R τ ∧ Matches value (BestCutIndex.best valid value count) τ)
      ((K+92)*count+10) := by
  have h1 : 1<B := by nlinarith
  have hstep : Spec B (fun σ => Invariant R valid value count σ ∧ σ.vars "cut.candidate"<count)
      (step producer) (fun σ τ => Invariant R valid value count τ ∧ τ.vars "cut.candidate"=σ.vars "cut.candidate"+1)
      (K+88) := by
    rintro σ ⟨⟨hR,hle,hmatch⟩,hlt⟩
    let i := σ.vars "cut.candidate"
    obtain ⟨ν,rp,pp⟩ := hproducer i hlt σ ⟨hR,rfl⟩
    have hm := Matches.frame rp hmatch hproducerFrame
    obtain ⟨μ,ru,pu⟩ := RamBestUpdate.command_spec B M valid value i (BestCutIndex.best valid value i) hB (hlt.trans hcount)
      (hvalue i hlt) (fun j hj => hvalue j ((BestCutIndex.best_sound valid value i j hj).1.trans hlt)) ν ⟨pp.2,hm⟩
    have hμ : μ.vars "cut.candidate"=i := pu.1.1
    have hnext : i+1<B := by dsimp [i]; omega
    let τ := μ.setVar "cut.candidate" (i+1)
    have ri : Run B (.assign "cut.candidate" (.add (.var "cut.candidate") (.lit 1))) μ τ 4 :=
      Run.assign (evalB_bin (op := .add) (by rw [evalB_var_iff]; exact ⟨hμ.symm,hμ ▸ (by omega : i<B)⟩)
        (evalB_lit h1) hnext)
    have hmatchτ := Matches.frame ri pu.2 (by dsimp [bestNames,Com.wvars]; decide)
    refine ⟨τ,rp.seq (ru.seq ri),?_,by simp [τ,i]⟩
    refine ⟨hset μ (i+1) "cut.candidate" (by simp) (hupdateFrame ru pp.1),by simp [τ]; dsimp [i]; omega,?_⟩
    simpa only [τ,vars_setVar,if_true,BestCutIndex.best] using hmatchτ
  have hs := Spec.forRangeZero "cut.candidate" "cut.count" (Invariant R valid value count) count (K+88)
    hcount (fun _ h => h.2.1) (fun σ h => hlimit σ h.1) hstep
  rintro σ hσ
  let ν := σ.setVar "best.found" 0
  let μ := ν.setVar "best.index" 0
  have rf : Run B (.assign "best.found" (.lit 0)) σ ν 2 := Run.assign (evalB_lit (by omega))
  have rix : Run B (.assign "best.index" (.lit 0)) ν μ 2 := Run.assign (evalB_lit (by omega))
  have hRμ := hset ν 0 "best.index" (by simp) (hset σ 0 "best.found" (by simp) hσ)
  have hinit : Invariant R valid value count (μ.setVar "cut.candidate" 0) := by
    refine ⟨hset μ 0 "cut.candidate" (by simp) hRμ,by simp,?_⟩
    simp [BestCutIndex.best,Matches,μ,ν,vars_setVar]
  obtain ⟨τ,rr,pr⟩ := hs μ hinit
  exact ⟨τ,(rf.seq (rix.seq rr)).mono (by simp only [Nat.add_assoc,Nat.reduceAdd]; omega),pr.1.1,by simpa only [pr.2] using pr.1.2.2⟩

end Lax455465Proofs.RamBestFold
