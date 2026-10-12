import Lax455465Proofs.RamBooleanArithmetic
import Lax455465Proofs.RamUnsignedVector
import Lax455465Proofs.MaskedMassData

namespace Lax455465Proofs.RamBooleanVector
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamVirtualState RamBooleanArithmetic
open scoped NNRat

def Context {n : ℕ} (leftArray rightArray : String) (a b : Fin n → Bool) (σ : Env) : Prop :=
  σ.vars "metric.n"=n ∧ Prefix (RamUnsignedBuffer.encode (MaskedMassData.flags a)) leftArray σ ∧
    Prefix (RamUnsignedBuffer.encode (MaskedMassData.flags b)) rightArray σ

def entry (mode : Option Bool) (leftArray rightArray : String) : Com := .seq (RamUnsignedBuffer.read leftArray "mask.i")
  (.seq (RamUnsignedArithmetic.copy "left") (.seq (RamUnsignedBuffer.read rightArray "mask.i")
    (.seq (RamUnsignedArithmetic.copy "right") (RamBooleanArithmetic.command mode))))

def command (mode : Option Bool) (leftArray rightArray target : String) : Com := .seq (.assign "mask.pos" (.lit 0))
  (RamUnsignedVector.command "mask.i" "metric.n" target "mask.pos" (entry mode leftArray rightArray))

theorem entry_spec (B : ℕ) {n : ℕ} (mode : Option Bool) (leftArray rightArray : String)
    (a b : Fin n → Bool) (v : Fin n) (h2 : 2<B) (hindex : 2*n+2<B) :
    Spec B (fun σ => Context leftArray rightArray a b σ ∧ σ.vars "mask.i"=v.val)
      (entry mode leftArray rightArray) (fun _ τ => Context leftArray rightArray a b τ ∧
        FractionOutput (bit (flag mode (a v) (b v)) : ℚ) τ) 50 := by
  have hnum (c : Bool) : (bit c).num<B := by cases c <;> simp [bit] <;> omega
  have hden (c : Bool) : (bit c).den=1 := by cases c <;> simp [bit]
  have hget (c : Fin n → Bool) : (MaskedMassData.flags c)[v.val]'(by simpa only [MaskedMassData.flags,List.length_ofFn] using v.isLt)=bit (c v) := by
    simp [MaskedMassData.flags,bit]
  rintro σ ⟨hσ,hidx⟩
  obtain ⟨ν,ra,pa⟩ := RamUnsignedBuffer.read_spec B leftArray "mask.i" (MaskedMassData.flags a) v.val
    (by simpa only [MaskedMassData.flags,List.length_ofFn] using v.isLt) h2 (by omega)
    (by rw [hget]; exact hnum _) (by rw [hget,hden]; omega) (by decide) σ ⟨hσ.2.1,hidx⟩
  obtain ⟨μ,rl,pl⟩ := RamUnsignedArithmetic.copy_spec B (bit (a v)) "left" (by omega) (hnum _) (by rw [hden]; omega) (by decide) ν
    (by simpa only [hget] using pa.1)
  have rprior := ra.seq rl
  obtain ⟨ξ,rb,pb⟩ := RamUnsignedBuffer.read_spec B rightArray "mask.i" (MaskedMassData.flags b) v.val
    (by simpa only [MaskedMassData.flags,List.length_ofFn] using v.isLt) h2 (by omega)
    (by rw [hget]; exact hnum _) (by rw [hget,hden]; omega) (by decide) μ
    ⟨by simpa only [Prefix,rprior.frame_arr rightArray (by change rightArray∉([] : List String); simp)] using hσ.2.2,
      (rprior.frame_var "mask.i" (by dsimp [entry,RamUnsignedBuffer.read,RamUnsignedArithmetic.copy,Com.wvars]; decide)).trans hidx⟩
  obtain ⟨η,rr,pr⟩ := RamUnsignedArithmetic.copy_spec B (bit (b v)) "right" (by omega) (hnum _) (by rw [hden]; omega) (by decide) ξ
    (by simpa only [hget] using pb.1)
  have ple : η.vars "left.s"=0 ∧ η.vars "left.n"=(bit (a v)).num ∧ η.vars "left.d"=1 := by
    have run := rb.seq rr
    simpa only [String.reduceAppend,hden,run.frame_var "left.s" (by dsimp [RamUnsignedBuffer.read,RamUnsignedArithmetic.copy,Com.wvars]; decide),run.frame_var "left.n" (by dsimp [RamUnsignedBuffer.read,RamUnsignedArithmetic.copy,Com.wvars]; decide),run.frame_var "left.d" (by dsimp [RamUnsignedBuffer.read,RamUnsignedArithmetic.copy,Com.wvars]; decide)] using pl
  obtain ⟨τ,rc,pc⟩ := RamBooleanArithmetic.command_spec B mode (a v) (b v) (by omega) η
    ⟨ple.1,ple.2.1,ple.2.2,by simpa only [String.reduceAppend,hden] using pr⟩
  have run := ra.seq (rl.seq (rb.seq (rr.seq rc)))
  refine ⟨τ,run,?_,pc⟩
  simpa only [Context,Prefix,run.frame_var "metric.n" (by dsimp [entry,RamUnsignedBuffer.read,RamUnsignedArithmetic.copy,RamBooleanArithmetic.command,Com.wvars]; cases mode <;> simp),
    run.frame_arr leftArray (by change leftArray∉([] : List String); simp),run.frame_arr rightArray (by change rightArray∉([] : List String); simp)] using hσ

set_option maxHeartbeats 1600000 in
/-- A fixed runtime vector loop computes Boolean intersections or directed
set differences from actual canonical membership buffers. -/
theorem command_spec (B : ℕ) {n : ℕ} (mode : Option Bool) (leftArray rightArray target : String)
    (a b : Fin n → Bool) (h2 : 2<B) (hindex : 2*n+2<B) (hfresh : leftArray≠target ∧ rightArray≠target) :
    Spec B (fun σ => Context leftArray rightArray a b σ ∧ 2*n<(σ.arrs target).length)
      (command mode leftArray rightArray target) (fun _ τ => Context leftArray rightArray a b τ ∧
        Prefix (RamUnsignedBuffer.encode (MaskedMassData.flags (fun v => flag mode (a v) (b v)))) target τ)
      (72*n+8) := by
  let qs := MaskedMassData.flags (fun v => flag mode (a v) (b v))
  have hlen : qs.length=n := List.length_ofFn
  have hv : ∀ i, ∀ hi : i<qs.length, qs[i]=bit (flag mode (a ⟨i,by simpa only [hlen] using hi⟩) (b ⟨i,by simpa only [hlen] using hi⟩)) := by
    intro i hi; simp [qs,MaskedMassData.flags,bit]
  have hb : ∀ i, ∀ hi : i<qs.length, qs[i].num<B ∧ qs[i].den<B := by
    intro i hi; rw [hv i hi]
    cases flag mode (a _) (b _) <;> simp [bit] <;> omega
  have body : ∀ i, ∀ hi : i<qs.length,
      Spec B (fun σ => Context leftArray rightArray a b σ ∧ σ.vars "mask.i"=i)
        (entry mode leftArray rightArray) (fun _ τ => Context leftArray rightArray a b τ ∧ FractionOutput (qs[i] : ℚ) τ) 50 := by
    intro i hi
    simpa only [hv i hi] using entry_spec B mode leftArray rightArray a b ⟨i,by simpa only [hlen] using hi⟩ h2 hindex
  have hf := RamUnsignedVector.command_spec B 50 (Context leftArray rightArray a b) "mask.i" "metric.n" target "mask.pos" qs []
    (entry mode leftArray rightArray) (by omega) (by simp only [List.length_nil,hlen]; omega)
    (fun i hi => (hb i hi).1) (fun i hi => (hb i hi).2) (fun _ h => by simpa only [hlen] using h.1)
    (fun σ k h => by simpa only [Context,Prefix,vars_setVar,arrs_setVar,String.reduceEq,if_false] using h) body
    (by dsimp [entry,RamUnsignedBuffer.read,RamUnsignedArithmetic.copy,RamBooleanArithmetic.command,Com.wvars]; cases mode <;> simp)
    (by dsimp [entry,RamUnsignedBuffer.read,RamUnsignedArithmetic.copy,RamBooleanArithmetic.command,Com.wvars]; cases mode <;> simp)
    (by change target∉([] : List String); simp) (by dsimp [RamUnsignedEncoding.command,RamWordBuffer.append,Com.wvars]; decide)
    (fun rr h => by
      simpa only [Context,Prefix,
        rr.frame_var "metric.n" (by dsimp [RamUnsignedEncoding.command,RamWordBuffer.append,Com.wvars]; decide),
        rr.frame_arr leftArray (by simp [RamUnsignedEncoding.command,RamWordBuffer.append,Com.warrs,hfresh.1]),
        rr.frame_arr rightArray (by simp [RamUnsignedEncoding.command,RamWordBuffer.append,Com.warrs,hfresh.2])] using h)
    (by decide) (by decide)
  rintro σ ⟨hσ,hroom⟩
  let ν := σ.setVar "mask.pos" 0
  have rz : Run B (.assign "mask.pos" (.lit 0)) σ ν 2 := Run.assign (evalB_lit (by omega))
  obtain ⟨τ,rr,pr⟩ := hf ν ⟨by simpa only [Context,Prefix,ν,vars_setVar,arrs_setVar,String.reduceEq,if_false] using hσ,
    by intro i hi; simp at hi,by simp [ν],by simpa only [ν,arrs_setVar,List.length_nil,Nat.zero_add,hlen] using hroom⟩
  exact ⟨τ,(rz.seq rr).mono (by simp only [hlen]; omega),pr.1,by simpa only [List.nil_append,qs] using pr.2.1⟩

end Lax455465Proofs.RamBooleanVector
