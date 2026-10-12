import Lax455465Proofs.RamUnsignedSum
import Lax455465Proofs.RamMaximum
import Lax455465Proofs.RamMinimum
import Lax455465Proofs.RamFrames

namespace Lax455465Proofs.RamUnsignedMaximum

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational
open scoped NNRat

def maximum (qs : List ℚ≥0) : ℚ≥0 := qs.foldr max 0

@[simp] theorem maximum_nil : maximum []=0 := rfl
@[simp] theorem maximum_cons (q : ℚ≥0) (qs : List ℚ≥0) : maximum (q::qs)=max q (maximum qs) := rfl

theorem maximum_append (as bs : List ℚ≥0) : maximum (as++bs)=max (maximum as) (maximum bs) := by
  induction as with
  | nil => simp [maximum]
  | cons a as ih => simp only [List.cons_append,maximum_cons,ih,max_assoc]

theorem maximum_height (M : ℕ) (qs : List ℚ≥0) (hM : 1 ≤ M)
    (hnum : ∀ q∈qs,q.num ≤ M) (hden : ∀ q∈qs,q.den ≤ M) :
    (maximum qs).num ≤ M ∧ (maximum qs).den ≤ M := by
  induction qs with
  | nil => simpa using And.intro (show 0 ≤ M by omega) hM
  | cons q qs ih =>
    have hq : q.num ≤ M ∧ q.den ≤ M := ⟨hnum q (by simp),hden q (by simp)⟩
    have ht := ih (fun x hx => hnum x (by simp [hx])) (fun x hx => hden x (by simp [hx]))
    by_cases hh : q ≤ maximum qs
    · simpa only [maximum_cons,max_eq_right hh] using ht
    · simpa only [maximum_cons,max_eq_left (le_of_not_ge hh)] using hq

def load : Com := .seq (.assign "right.s" (.lit 0))
  (.seq (.assign "right.n" (.var "maximum.n")) (.assign "right.d" (.var "maximum.d")))
def save : Com := .seq (.assign "maximum.n" (.var "rat.n")) (.assign "maximum.d" (.var "rat.d"))
def finish : Com := .seq (.assign "rat.s" (.lit 0))
  (.seq (.assign "rat.n" (.var "maximum.n")) (.assign "rat.d" (.var "maximum.d")))
def init : Com := .seq (.assign "maximum.n" (.lit 0)) (.assign "maximum.d" (.lit 1))

def Stored (q : ℚ≥0) (σ : Env) : Prop := σ.vars "maximum.n" = q.num ∧ σ.vars "maximum.d" = q.den

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
  (.seq load (.seq RamMaximum.command save))
def step (index : String) (body : Com) : Com := .seq body
  (.seq combine (.assign index (.add (.var index) (.lit 1))))
def command (index limit : String) (body : Com) : Com := .seq init
  (.seq (.seq (.assign index (.lit 0)) (.while (.lt (.var index) (.var limit)) (step index body))) finish)

/-- One comparison step retains the exact maximum and retains its unsigned
representation for the next step. -/
theorem combine_spec (B M : ℕ) (a b : ℚ≥0) (hB : 2*M^2+3 < B)
    (han : a.num ≤ M) (had : a.den ≤ M) (hbn : b.num ≤ M) (hbd : b.den ≤ M)
    (hsn : (max a b).num < B) (hsd : (max a b).den < B) :
    Spec B (fun σ => FractionOutput (a : ℚ) σ ∧ Stored b σ) combine
      (fun _ τ => Stored (max a b) τ) 66 := by
  have hM : M < B := by nlinarith
  have h1 : 1 < B := by nlinarith
  rintro σ ⟨ha,hb⟩
  obtain ⟨ν,rleft,pleft⟩ := RamUnsignedArithmetic.copy_spec B a "left" h1
    (han.trans_lt hM) (had.trans_lt hM) (by decide) σ ha
  have hbν : Stored b ν := by
    simpa only [Stored,rleft.frame_var "maximum.n" (by decide),rleft.frame_var "maximum.d" (by decide)] using hb
  obtain ⟨μ,rright,pright⟩ := load_spec B b h1 (hbn.trans_lt hM) (hbd.trans_lt hM) ν hbν
  have paμ : μ.vars "left.s" = 0 ∧ μ.vars "left.n" = a.num ∧ μ.vars "left.d" = a.den := by
    simpa only [rright.frame_var "left.s" (by decide),rright.frame_var "left.n" (by decide),rright.frame_var "left.d" (by decide),String.reduceAppend] using pleft
  obtain ⟨ξ,radd,padd⟩ := RamMaximum.command_spec B M a b hB han had hbn hbd μ
    ⟨paμ.1,paμ.2.1,paμ.2.2,pright⟩
  obtain ⟨τ,rsave,psave⟩ := save_spec B (max a b) hsn hsd ξ (by simpa only [NNRat.coe_max] using padd)
  exact ⟨τ,rleft.seq (rright.seq (radd.seq rsave)),psave⟩

def Invariant (R : Env → Prop) (index : String) (qs : List ℚ≥0) (σ : Env) : Prop :=
  R σ ∧ σ.vars index ≤ qs.length ∧ Stored (maximum (qs.take (σ.vars index))) σ

set_option maxHeartbeats 800000 in
/-- Exact bounded native maximum of nonnegative rationals. Every intermediate
maximum is zero or an entry of the input list, so its height never grows. -/
theorem command_spec (B M K : ℕ) (R : Env → Prop) (index limit : String)
    (qs : List ℚ≥0) (body : Com) (hB : 2*M^2+3 < B) (hlen : qs.length < B)
    (hnum : ∀ q ∈ qs, q.num ≤ M) (hden : ∀ q ∈ qs, q.den ≤ M)
    (hprefixNum : ∀ i, (maximum (qs.take i)).num ≤ M) (hprefixDen : ∀ i, (maximum (qs.take i)).den ≤ M)
    (hlimit : ∀ σ, R σ → σ.vars limit = qs.length)
    (hset : ∀ σ k name, R σ → name = index ∨ name = "maximum.n" ∨ name = "maximum.d" → R (σ.setVar name k))
    (hbody : ∀ i, ∀ hi : i < qs.length,
      Spec B (fun σ => R σ ∧ σ.vars index = i) body
        (fun _ τ => R τ ∧ FractionOutput (qs[i] : ℚ) τ) K)
    (hfresh : index ≠ "maximum.n" ∧ index ≠ "maximum.d" ∧ index ∉ combine.wvars)
    (hbodyIndex : index ∉ body.wvars) (hbodySum : "maximum.n" ∉ body.wvars ∧ "maximum.d" ∉ body.wvars)
    (hcombineFrame : ∀ {σ τ : Env} {k : ℕ}, Run B combine σ τ k → R σ → R τ)
    (hfinishFrame : ∀ {σ τ : Env} {k : ℕ}, Run B finish σ τ k → R σ → R τ) :
    Spec B R (command index limit body)
      (fun _ τ => R τ ∧ FractionOutput ((maximum qs : ℚ≥0) : ℚ) τ)
      ((K+74)*qs.length+16) := by
  have hM : M < B := by nlinarith
  have h1 : 1 < B := by nlinarith
  have hstep : Spec B (fun σ => Invariant R index qs σ ∧ σ.vars index < qs.length)
      (step index body) (fun σ τ => Invariant R index qs τ ∧ τ.vars index = σ.vars index+1)
      (K+70) := by
    rintro σ ⟨⟨hR,hi,hstored⟩,hlt⟩
    let i := σ.vars index
    have hi' : i < qs.length := hlt
    obtain ⟨ν,rbody,pbody⟩ := hbody i hi' σ ⟨hR,rfl⟩
    have hiν : ν.vars index = i := (rbody.frame_var index hbodyIndex).trans rfl
    have hstoredν : Stored (maximum (qs.take i)) ν := by
      simpa only [Stored,rbody.frame_var "maximum.n" hbodySum.1,rbody.frame_var "maximum.d" hbodySum.2] using hstored
    have hq : qs[i] ∈ qs := List.getElem_mem hi'
    have hsum : max qs[i] (maximum (qs.take i))=maximum (qs.take (i+1)) := by
      rw [List.take_succ_eq_append_getElem hi',maximum_append]
      rw [maximum_cons,maximum_nil,max_eq_left (show (0 : ℚ≥0) ≤ qs[i] by positivity),max_comm]
    obtain ⟨μ,rcombine,pcombine⟩ := combine_spec B M qs[i] (maximum (qs.take i)) hB
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
  have hscan := Spec.forRangeZero index limit (Invariant R index qs) qs.length
    (K+70) hlen (fun _ h => h.2.1) (fun σ h => hlimit σ h.1) hstep
  rintro σ hR
  let ν := (σ.setVar "maximum.n" 0).setVar "maximum.d" 1
  have rinit : Run B init σ ν 4 := by
    exact (Run.assign (evalB_lit (by omega : 0 < B))).seq (Run.assign (evalB_lit h1))
  have hRν : R ν := hset _ 1 "maximum.d" (hset σ 0 "maximum.n" hR (Or.inr (Or.inl rfl))) (Or.inr (Or.inr rfl))
  have hinvariant : Invariant R index qs (ν.setVar index 0) := by
    refine ⟨hset ν 0 index hRν (Or.inl rfl),by simp,?_⟩
    simp [Stored,ν,Ne.symm hfresh.1,Ne.symm hfresh.2.1]
  obtain ⟨μ,rscan,pscan⟩ := hscan ν hinvariant
  have hstoredμ : Stored (maximum qs) μ := by simpa only [pscan.2,List.take_length] using pscan.1.2.2
  have hfinalNum : (maximum qs).num ≤ M := by simpa only [List.take_length] using hprefixNum qs.length
  have hfinalDen : (maximum qs).den ≤ M := by simpa only [List.take_length] using hprefixDen qs.length
  obtain ⟨τ,rfinish,pfinish⟩ := finish_spec B (maximum qs) h1 (hfinalNum.trans_lt hM) (hfinalDen.trans_lt hM) μ hstoredμ
  refine ⟨τ,(rinit.seq (rscan.seq rfinish)).mono (by simp only [Nat.add_assoc,Nat.reduceAdd]; omega),hfinishFrame rfinish pscan.1.1,pfinish⟩

end Lax455465Proofs.RamUnsignedMaximum
