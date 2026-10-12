import Lax455465Proofs.RamUnsignedSum
import Lax455465Proofs.Bottleneck
import Lax455465Proofs.RamUnsignedScalar
import Lax455465Proofs.RamMinimum
import Lax455465Proofs.RamFrames

namespace Lax455465Proofs.RamBottleneckFold

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational
open scoped NNRat

def load : Com := .seq (.assign "right.s" (.lit 0))
  (.seq (.assign "right.n" (.var "minimum.n")) (.assign "right.d" (.var "minimum.d")))
def save : Com := .seq (.assign "minimum.n" (.var "rat.n")) (.assign "minimum.d" (.var "rat.d"))
def finish : Com := .seq (.assign "rat.s" (.lit 0))
  (.seq (.assign "rat.n" (.var "minimum.n")) (.assign "rat.d" (.var "minimum.d")))
def init : Com := .seq (.assign "minimum.n" (.var "short.remaining.n"))
  (.assign "minimum.d" (.var "short.remaining.d"))

def Stored (q : ℚ≥0) (σ : Env) : Prop := σ.vars "minimum.n" = q.num ∧ σ.vars "minimum.d" = q.den

theorem load_spec (B : ℕ) (q : ℚ≥0) (h1 : 1 < B) (hn : q.num < B) (hd : q.den < B) :
    Spec B (Stored q) load (fun _ τ => τ.vars "right.s" = 0 ∧ τ.vars "right.n" = q.num ∧ τ.vars "right.d" = q.den) 6 := by
  rintro σ ⟨hnσ,hdσ⟩
  run_vcg
  all_goals simp_all [Stored]

theorem save_spec (B : ℕ) (q : ℚ≥0) (hn : q.num < B) (hd : q.den < B) :
    Spec B (FractionOutput (q : ℚ)) save (fun _ τ => Stored q τ) 4 := by
  rintro σ ⟨hv,hnσ,hdσ,hs⟩
  have hn' : σ.vars "rat.n" = q.num := by simpa only [NNRat.natAbs_num_coe] using hnσ
  have hd' : σ.vars "rat.d" = q.den := by simpa only [NNRat.den_coe] using hdσ
  run_vcg
  all_goals simp_all [Stored]

theorem finish_spec (B : ℕ) (q : ℚ≥0) (h1 : 1 < B) (hn : q.num < B) (hd : q.den < B) :
    Spec B (Stored q) finish (fun _ τ => FractionOutput (q : ℚ) τ) 6 := by
  rintro σ ⟨hnσ,hdσ⟩
  have hv := RamUnsignedArithmetic.value q
  run_vcg
  all_goals simp_all [Stored,FractionOutput,NNRat.natAbs_num_coe,NNRat.den_coe]

def combine : Com := .seq (RamUnsignedArithmetic.copy "left")
  (.seq load (.seq RamMinimum.command save))
def step (index : String) (body : Com) : Com := .seq body
  (.seq combine (.assign index (.add (.var index) (.lit 1))))
def command (index limit : String) (body : Com) : Com := .seq init
  (.seq (.seq (.assign index (.lit 0)) (.while (.lt (.var index) (.var limit)) (step index body))) finish)

/-- One comparison step retains the exact minimum and its unsigned
representation for the next step. -/
theorem combine_spec (B M : ℕ) (a b : ℚ≥0) (hB : 2*M^2+3 < B)
    (han : a.num ≤ M) (had : a.den ≤ M) (hbn : b.num ≤ M) (hbd : b.den ≤ M)
    (hsn : (min a b).num < B) (hsd : (min a b).den < B) :
    Spec B (fun σ => FractionOutput (a : ℚ) σ ∧ Stored b σ) combine
      (fun _ τ => Stored (min a b) τ) 66 := by
  have hM : M < B := by nlinarith
  have h1 : 1 < B := by nlinarith
  rintro σ ⟨ha,hb⟩
  obtain ⟨ν,rleft,pleft⟩ := RamUnsignedArithmetic.copy_spec B a "left" h1
    (han.trans_lt hM) (had.trans_lt hM) (by decide) σ ha
  have hbν : Stored b ν := by
    simpa only [Stored,rleft.frame_var "minimum.n" (by decide),rleft.frame_var "minimum.d" (by decide)] using hb
  obtain ⟨μ,rright,pright⟩ := load_spec B b h1 (hbn.trans_lt hM) (hbd.trans_lt hM) ν hbν
  have paμ : μ.vars "left.s" = 0 ∧ μ.vars "left.n" = a.num ∧ μ.vars "left.d" = a.den := by
    simpa only [rright.frame_var "left.s" (by decide),rright.frame_var "left.n" (by decide),rright.frame_var "left.d" (by decide),String.reduceAppend] using pleft
  obtain ⟨ξ,radd,padd⟩ := RamMinimum.command_spec B M a b hB han had hbn hbd μ
    ⟨paμ.1,paμ.2.1,paμ.2.2,pright⟩
  obtain ⟨τ,rsave,psave⟩ := save_spec B (min a b) hsn hsd ξ (by simpa only [NNRat.coe_min] using padd)
  exact ⟨τ,rleft.seq (rright.seq (radd.seq rsave)),psave⟩

def Invariant (R : Env → Prop) (index : String) (a : ℚ≥0) (qs : List ℚ≥0) (σ : Env) : Prop :=
  R σ ∧ σ.vars index ≤ qs.length ∧ Stored (Bottleneck.minimum a (qs.take (σ.vars index))) σ

set_option maxHeartbeats 800000 in
/-- Exact native bottleneck fold, initialized with the remaining commodity
demand. Each minimum is that initial amount or an actual residual coordinate. -/
theorem command_spec (B M K : ℕ) (R : Env → Prop) (index limit : String)
    (a : ℚ≥0) (qs : List ℚ≥0) (body : Com) (hB : 2*M^2+3 < B) (hlen : qs.length < B)
    (hnum : ∀ q ∈ qs, q.num ≤ M) (hden : ∀ q ∈ qs, q.den ≤ M)
    (ha : a.num≤M ∧ a.den≤M)
    (hlimit : ∀ σ, R σ → σ.vars limit = qs.length)
    (hset : ∀ σ k name, R σ → name = index ∨ name = "minimum.n" ∨ name = "minimum.d" → R (σ.setVar name k))
    (hbody : ∀ i, ∀ hi : i < qs.length,
      Spec B (fun σ => R σ ∧ σ.vars index = i) body
        (fun _ τ => R τ ∧ FractionOutput (qs[i] : ℚ) τ) K)
    (hfresh : index ≠ "minimum.n" ∧ index ≠ "minimum.d" ∧ index ∉ combine.wvars)
    (hbodyIndex : index ∉ body.wvars) (hbodySum : "minimum.n" ∉ body.wvars ∧ "minimum.d" ∉ body.wvars)
    (hcombineFrame : ∀ {σ τ : Env} {k : ℕ}, Run B combine σ τ k → R σ → R τ)
    (hfinishFrame : ∀ {σ τ : Env} {k : ℕ}, Run B finish σ τ k → R σ → R τ) :
    Spec B (fun σ => R σ ∧ RamUnsignedScalar.Stored "short.remaining" a σ) (command index limit body)
      (fun _ τ => R τ ∧ FractionOutput ((Bottleneck.minimum a qs : ℚ≥0) : ℚ) τ)
      ((K+74)*qs.length+16) := by
  have hM : M < B := by nlinarith
  have h1 : 1 < B := by nlinarith
  have hprefix (i : ℕ) := Bottleneck.height M a (qs.take i) ha
    (fun q hq => ⟨hnum q (List.mem_of_mem_take hq),hden q (List.mem_of_mem_take hq)⟩)
  have hprefixNum := fun i => (hprefix i).1
  have hprefixDen := fun i => (hprefix i).2
  have hstep : Spec B (fun σ => Invariant R index a qs σ ∧ σ.vars index < qs.length)
      (step index body) (fun σ τ => Invariant R index a qs τ ∧ τ.vars index = σ.vars index+1)
      (K+70) := by
    rintro σ ⟨⟨hR,hi,hstored⟩,hlt⟩
    let i := σ.vars index
    have hi' : i < qs.length := hlt
    obtain ⟨ν,rbody,pbody⟩ := hbody i hi' σ ⟨hR,rfl⟩
    have hiν : ν.vars index = i := (rbody.frame_var index hbodyIndex).trans rfl
    have hstoredν : Stored (Bottleneck.minimum a (qs.take i)) ν := by
      simpa only [Stored,rbody.frame_var "minimum.n" hbodySum.1,rbody.frame_var "minimum.d" hbodySum.2] using hstored
    have hq : qs[i] ∈ qs := List.getElem_mem hi'
    have hsum : min qs[i] (Bottleneck.minimum a (qs.take i))=Bottleneck.minimum a (qs.take (i+1)) := by
      rw [List.take_succ_eq_append_getElem hi',Bottleneck.append,Bottleneck.minimum_cons,Bottleneck.minimum_nil,min_comm]
    obtain ⟨μ,rcombine,pcombine⟩ := combine_spec B M qs[i] (Bottleneck.minimum a (qs.take i)) hB
      (hnum _ hq) (hden _ hq) (hprefixNum i) (hprefixDen i)
      (by rw [hsum]; exact (hprefixNum (i+1)).trans_lt hM)
      (by rw [hsum]; exact (hprefixDen (i+1)).trans_lt hM) ν ⟨pbody.2,hstoredν⟩
    have hiμ : μ.vars index = i := (rcombine.frame_var index hfresh.2.2).trans hiν
    have hRμ := hcombineFrame rcombine pbody.1
    have hinc : Run B (.assign index (.add (.var index) (.lit 1))) μ (μ.setVar index (i+1)) 4 :=
      Run.assign (evalB_bin (op := .add) (by rw [evalB_var_iff]; exact ⟨hiμ.symm,hiμ ▸ (by omega : i < B)⟩)
        (evalB_lit h1) (by dsimp [Bop.apply]; omega))
    refine ⟨μ.setVar index (i+1),(rbody.seq (rcombine.seq hinc)).mono (by omega),?_,?_⟩
    · refine ⟨hset μ (i+1) index hRμ (Or.inl rfl),by simp; omega,?_⟩
      simpa only [Stored,vars_setVar,if_neg (Ne.symm hfresh.1),if_neg (Ne.symm hfresh.2.1),if_pos rfl,if_true,hsum] using pcombine
    · simp [i]
  have hscan := Spec.forRangeZero index limit (Invariant R index a qs) qs.length
    (K+70) hlen (fun _ h => h.2.1) (fun σ h => hlimit σ h.1) hstep
  rintro σ ⟨hR,hremaining⟩
  let ν := (σ.setVar "minimum.n" a.num).setVar "minimum.d" a.den
  have rinit : Run B init σ ν 4 := by
    have hn : σ.vars "short.remaining.n"=a.num := hremaining.1
    have hd : σ.vars "short.remaining.d"=a.den := hremaining.2
    exact (Run.assign (by rw [evalB_var_iff]; exact ⟨hn.symm,hn ▸ ha.1.trans_lt hM⟩)).seq
      (Run.assign (by rw [evalB_var_iff]; exact ⟨by simpa only [vars_setVar,String.reduceEq,if_false] using hd.symm,
        by simpa only [vars_setVar,String.reduceEq,if_false] using hd ▸ ha.2.trans_lt hM⟩))
  have hRν : R ν := hset _ a.den "minimum.d" (hset σ a.num "minimum.n" hR (Or.inr (Or.inl rfl))) (Or.inr (Or.inr rfl))
  have hinvariant : Invariant R index a qs (ν.setVar index 0) := by
    refine ⟨hset ν 0 index hRν (Or.inl rfl),by simp,?_⟩
    simp [Stored,ν,Bottleneck.minimum_nil,Ne.symm hfresh.1,Ne.symm hfresh.2.1]
  obtain ⟨μ,rscan,pscan⟩ := hscan ν hinvariant
  have hstoredμ : Stored (Bottleneck.minimum a qs) μ := by simpa only [pscan.2,List.take_length] using pscan.1.2.2
  have hfinalNum : (Bottleneck.minimum a qs).num ≤ M := by simpa only [List.take_length] using hprefixNum qs.length
  have hfinalDen : (Bottleneck.minimum a qs).den ≤ M := by simpa only [List.take_length] using hprefixDen qs.length
  obtain ⟨τ,rfinish,pfinish⟩ := finish_spec B (Bottleneck.minimum a qs) h1 (hfinalNum.trans_lt hM) (hfinalDen.trans_lt hM) μ hstoredμ
  refine ⟨τ,(rinit.seq (rscan.seq rfinish)).mono (by simp only [Nat.add_assoc,Nat.reduceAdd]; omega),hfinishFrame rfinish pscan.1.1,pfinish⟩

end Lax455465Proofs.RamBottleneckFold
