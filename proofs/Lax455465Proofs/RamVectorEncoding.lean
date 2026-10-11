import Lax455465Proofs.RamFractionEncoding

namespace Lax455465Proofs.RamVectorEncoding

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState
open Lax109476.RationalEncoding

def encode (qs : List ℚ) : List ℕ := qs.flatMap encodeRational

@[simp] theorem length_encode (qs : List ℚ) : (encode qs).length = 3*qs.length := by
  induction qs with
  | nil => rfl
  | cons q qs ih =>
    simp only [encode] at ih
    simp [encode,encodeRational,ih]; omega

def step (index : String) (body : Com) : Com := .seq body
  (.seq RamFractionEncoding.emit (.assign index (.add (.var index) (.lit 1))))

def command (index limit : String) (body : Com) : Com :=
  .seq (.assign index (.lit 0)) (.while (.lt (.var index) (.var limit)) (step index body))

def Invariant (R : Env → Prop) (index : String) (qs : List ℚ) (words : List ℕ) (σ : Env) : Prop :=
  R σ ∧ σ.vars index ≤ qs.length ∧
    Prefix (words ++ encode (qs.take (σ.vars index))) "lp.word" σ ∧
    σ.vars "lp.position" = words.length+3*σ.vars index ∧
    words.length+3*qs.length < (σ.arrs "lp.word").length

/-- A bounded runtime vector loop emits the exact rational word, retaining
its initialized prefix. The coefficient producer is a fixed native command;
its hypotheses are ordinary execution and frame proofs. -/
theorem command_spec (B K : ℕ) (R : Env → Prop) (index limit : String)
    (qs : List ℚ) (words : List ℕ) (body : Com) (h1 : 1 < B)
    (hlen : words.length+3*qs.length+3 < B)
    (hnum : ∀ i, ∀ hi : i < qs.length, qs[i].num.natAbs < B)
    (hden : ∀ i, ∀ hi : i < qs.length, qs[i].den < B)
    (hlimit : ∀ σ, R σ → σ.vars limit = qs.length)
    (hset : ∀ σ k, R σ → R (σ.setVar index k))
    (hbody : ∀ i, ∀ hi : i < qs.length,
      Spec B (fun σ => R σ ∧ σ.vars index = i) body
        (fun _ τ => R τ ∧ RamRational.FractionOutput qs[i] τ) K)
    (hbodyIndex : index ∉ body.wvars) (hbodyPosition : "lp.position" ∉ body.wvars)
    (hbodyArray : "lp.word" ∉ body.warrs)
    (hemitIndex : index ∉ RamFractionEncoding.emit.wvars)
    (hemitFrame : ∀ {σ τ : Env} {k : ℕ}, Run B RamFractionEncoding.emit σ τ k → R σ → R τ)
    (hpositionIndex : index ≠ "lp.position") :
    Spec B (fun σ => R σ ∧ Prefix words "lp.word" σ ∧ σ.vars "lp.position" = words.length ∧
      words.length+3*qs.length < (σ.arrs "lp.word").length) (command index limit body)
      (fun _ τ => R τ ∧ Prefix (words ++ encode qs) "lp.word" τ ∧
        τ.vars "lp.position" = words.length+3*qs.length) ((K+35)*qs.length+6) := by
  have hcount : qs.length < B := by omega
  have hstep : Spec B (fun σ => Invariant R index qs words σ ∧ σ.vars index < qs.length)
      (step index body) (fun σ τ => Invariant R index qs words τ ∧ τ.vars index = σ.vars index+1)
      (K+31) := by
    rintro σ ⟨⟨hR,hi,hp,hpos,hroom⟩,hlt⟩
    let i := σ.vars index
    have hi' : i < qs.length := hlt
    have hi0 : i ≤ qs.length := hi
    have hpLen : (words ++ encode (qs.take i)).length = words.length+3*i := by
      simp only [List.length_append,length_encode,List.length_take,Nat.min_eq_left hi0]
    obtain ⟨ν,hproduce,hproduced⟩ := hbody i hi' σ ⟨hR,rfl⟩
    have hiν : ν.vars index = i := (hproduce.frame_var index hbodyIndex).trans rfl
    have hposν : ν.vars "lp.position" = words.length+3*i :=
      (hproduce.frame_var "lp.position" hbodyPosition).trans hpos
    have hpν : Prefix (words ++ encode (qs.take i)) "lp.word" ν := by
      simpa only [Prefix,hproduce.frame_arr "lp.word" hbodyArray] using hp
    have hroomν : words.length+3*qs.length < (ν.arrs "lp.word").length := by
      rwa [RamFrames.run_array_length hproduce "lp.word"]
    obtain ⟨μ,hemit,hemitted⟩ := RamFractionEncoding.emit_spec B qs[i] (words ++ encode (qs.take i)) h1
      (hnum i hi') (hden i hi') (by rw [hpLen]; omega) ν
        ⟨hproduced.2,hpν,by rwa [hpLen],by rw [hpLen]; omega⟩
    have hiμ : μ.vars index = i := (hemit.frame_var index hemitIndex).trans hiν
    have hRμ := hemitFrame hemit hproduced.1
    have hroomμ : words.length+3*qs.length < (μ.arrs "lp.word").length := by
      rwa [RamFrames.run_array_length hemit "lp.word"]
    have hpμ : Prefix (words ++ encode (qs.take (i+1))) "lp.word" μ := by
      rw [List.take_succ_eq_append_getElem hi']
      simpa only [encode,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,
        List.append_assoc] using hemitted.1
    have hposμ : μ.vars "lp.position" = words.length+3*(i+1) := by rw [hpLen] at hemitted; omega
    have hnext : i+1 < B := by omega
    have hinc : Run B (.assign index (.add (.var index) (.lit 1))) μ (μ.setVar index (i+1)) 4 :=
      Run.assign (evalB_bin (op := .add) (by rw [evalB_var_iff]; exact ⟨hiμ.symm,hiμ ▸ (by omega : i < B)⟩)
        (evalB_lit h1) hnext)
    refine ⟨μ.setVar index (i+1),hproduce.seq (hemit.seq hinc),?_,?_⟩
    · refine ⟨hset μ (i+1) hRμ,by simp; omega,?_,?_,?_⟩
      · simpa only [Prefix,arrs_setVar,vars_setVar,if_pos rfl,if_true] using hpμ
      · simpa only [vars_setVar,if_neg (Ne.symm hpositionIndex),if_true] using hposμ
      · simpa only [arrs_setVar] using hroomμ
    · simp [i]
  have hscan := Spec.forRangeZero index limit (Invariant R index qs words) qs.length (K+31)
    hcount (fun _ h => h.2.1) (fun σ h => hlimit σ h.1) hstep
  rintro σ ⟨hR,hp,hpos,hroom⟩
  have hinit : Invariant R index qs words (σ.setVar index 0) := by
    refine ⟨hset σ 0 hR,by simp,?_,?_,?_⟩
    · simpa only [Prefix,arrs_setVar,vars_setVar,if_pos rfl,if_true,List.take_zero,encode,List.flatMap_nil,
        List.append_nil] using hp
    · simpa only [vars_setVar,if_neg (Ne.symm hpositionIndex),if_true,Nat.mul_zero,Nat.add_zero] using hpos
    · simpa only [arrs_setVar] using hroom
  obtain ⟨τ,hr,hpost⟩ := hscan σ hinit
  refine ⟨τ,by simpa [command,Nat.add_assoc] using hr,hpost.1.1,?_,?_⟩
  · simpa only [hpost.2,List.take_length] using hpost.1.2.2.1
  · simpa only [hpost.2] using hpost.1.2.2.2.1

end Lax455465Proofs.RamVectorEncoding
