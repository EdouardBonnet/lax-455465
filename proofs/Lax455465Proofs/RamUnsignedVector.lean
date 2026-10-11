import Lax455465Proofs.RamUnsignedEncoding

namespace Lax455465Proofs.RamUnsignedVector

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState
open Lax455465.RationalEncoding
open scoped NNRat

def step (index array cursor : String) (body : Com) : Com := .seq body
  (.seq (RamUnsignedEncoding.command array cursor) (.assign index (.add (.var index) (.lit 1))))

def command (index limit array cursor : String) (body : Com) : Com :=
  .seq (.assign index (.lit 0)) (.while (.lt (.var index) (.var limit)) (step index array cursor body))

def Invariant (R : Env → Prop) (index : String) (qs : List ℚ≥0) (words : List ℕ) (array cursor : String) (σ : Env) : Prop :=
  R σ ∧ σ.vars index ≤ qs.length ∧
    Prefix (words ++ RamUnsignedBuffer.encode (qs.take (σ.vars index))) array σ ∧
    σ.vars cursor = words.length+2*σ.vars index ∧
    words.length+2*qs.length < (σ.arrs array).length

/-- A bounded runtime vector loop emits the exact rational word, retaining
its initialized prefix. The coefficient producer is a fixed native command;
its hypotheses are ordinary execution and frame proofs. -/
theorem command_spec (B K : ℕ) (R : Env → Prop) (index limit array cursor : String)
    (qs : List ℚ≥0) (words : List ℕ) (body : Com) (h1 : 1 < B)
    (hlen : words.length+2*qs.length+2 < B)
    (hnum : ∀ i, ∀ hi : i < qs.length, qs[i].num < B)
    (hden : ∀ i, ∀ hi : i < qs.length, qs[i].den < B)
    (hlimit : ∀ σ, R σ → σ.vars limit = qs.length)
    (hset : ∀ σ k, R σ → R (σ.setVar index k))
    (hbody : ∀ i, ∀ hi : i < qs.length,
      Spec B (fun σ => R σ ∧ σ.vars index = i) body
        (fun _ τ => R τ ∧ RamRational.FractionOutput (qs[i] : ℚ) τ) K)
    (hbodyIndex : index ∉ body.wvars) (hbodyPosition : cursor ∉ body.wvars)
    (hbodyArray : array ∉ body.warrs)
    (hemitIndex : index ∉ (RamUnsignedEncoding.command array cursor).wvars)
    (hemitFrame : ∀ {σ τ : Env} {k : ℕ}, Run B (RamUnsignedEncoding.command array cursor) σ τ k → R σ → R τ)
    (hpositionIndex : index ≠ cursor) (hcursorDen : cursor ≠ "rat.d") :
    Spec B (fun σ => R σ ∧ Prefix words array σ ∧ σ.vars cursor = words.length ∧
      words.length+2*qs.length < (σ.arrs array).length) (command index limit array cursor body)
      (fun _ τ => R τ ∧ Prefix (words ++ RamUnsignedBuffer.encode qs) array τ ∧
        τ.vars cursor = words.length+2*qs.length) ((K+22)*qs.length+6) := by
  have hcount : qs.length < B := by omega
  have hstep : Spec B (fun σ => Invariant R index qs words array cursor σ ∧ σ.vars index < qs.length)
      (step index array cursor body) (fun σ τ => Invariant R index qs words array cursor τ ∧ τ.vars index = σ.vars index+1)
      (K+18) := by
    rintro σ ⟨⟨hR,hi,hp,hpos,hroom⟩,hlt⟩
    let i := σ.vars index
    have hi' : i < qs.length := hlt
    have hi0 : i ≤ qs.length := hi
    have hpLen : (words ++ RamUnsignedBuffer.encode (qs.take i)).length = words.length+2*i := by
      simp only [List.length_append,RamUnsignedBuffer.length_encode,List.length_take,Nat.min_eq_left hi0]
    obtain ⟨ν,hproduce,hproduced⟩ := hbody i hi' σ ⟨hR,rfl⟩
    have hiν : ν.vars index = i := (hproduce.frame_var index hbodyIndex).trans rfl
    have hposν : ν.vars cursor = words.length+2*i :=
      (hproduce.frame_var cursor hbodyPosition).trans hpos
    have hpν : Prefix (words ++ RamUnsignedBuffer.encode (qs.take i)) array ν := by
      simpa only [Prefix,hproduce.frame_arr array hbodyArray] using hp
    have hroomν : words.length+2*qs.length < (ν.arrs array).length := by
      rwa [RamFrames.run_array_length hproduce array]
    obtain ⟨μ,hemit,hemitted⟩ := RamUnsignedEncoding.command_spec B array cursor qs[i] (words ++ RamUnsignedBuffer.encode (qs.take i)) h1
      (hnum i hi') (hden i hi') (by rw [hpLen]; omega) hcursorDen ν
        ⟨hproduced.2,hpν,by rwa [hpLen],by rw [hpLen]; omega⟩
    have hiμ : μ.vars index = i := (hemit.frame_var index hemitIndex).trans hiν
    have hRμ := hemitFrame hemit hproduced.1
    have hroomμ : words.length+2*qs.length < (μ.arrs array).length := by
      rwa [RamFrames.run_array_length hemit array]
    have hpμ : Prefix (words ++ RamUnsignedBuffer.encode (qs.take (i+1))) array μ := by
      rw [List.take_succ_eq_append_getElem hi']
      simpa only [RamUnsignedBuffer.encode,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,
        List.append_assoc] using hemitted.1
    have hposμ : μ.vars cursor = words.length+2*(i+1) := by rw [hpLen] at hemitted; omega
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
  have hscan := Spec.forRangeZero index limit (Invariant R index qs words array cursor) qs.length (K+18)
    hcount (fun _ h => h.2.1) (fun σ h => hlimit σ h.1) hstep
  rintro σ ⟨hR,hp,hpos,hroom⟩
  have hinit : Invariant R index qs words array cursor (σ.setVar index 0) := by
    refine ⟨hset σ 0 hR,by simp,?_,?_,?_⟩
    · simpa only [Prefix,arrs_setVar,vars_setVar,if_pos rfl,if_true,List.take_zero,RamUnsignedBuffer.encode,List.flatMap_nil,
        List.append_nil] using hp
    · simpa only [vars_setVar,if_neg (Ne.symm hpositionIndex),if_true,Nat.mul_zero,Nat.add_zero] using hpos
    · simpa only [arrs_setVar] using hroom
  obtain ⟨τ,hr,hpost⟩ := hscan σ hinit
  refine ⟨τ,by simpa [command,Nat.add_assoc] using hr,hpost.1.1,?_,?_⟩
  · simpa only [hpost.2,List.take_length] using hpost.1.2.2.1
  · simpa only [hpost.2] using hpost.1.2.2.2.1

end Lax455465Proofs.RamUnsignedVector
