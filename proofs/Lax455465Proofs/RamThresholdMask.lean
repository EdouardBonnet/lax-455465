import Lax455465Proofs.RamArrayScalar
import Lax455465Proofs.RamScalarComparison
import Lax455465Proofs.RamUnsignedVector
import Lax455465Proofs.MaskedMassData
import Lax455465Proofs.RamRoundingConstants

namespace Lax455465Proofs.RamThresholdMask
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar RamRational RamBooleanArithmetic
open scoped NNRat

def chosen (reversed : Bool) (a threshold : ℚ≥0) : Bool :=
  decide (if reversed then (threshold : ℚ)≤a else (a : ℚ)≤threshold)
def Context {n : ℕ} (potential : Fin n → ℚ≥0) (threshold : ℚ≥0) (σ : Env) : Prop :=
  σ.vars "metric.n"=n ∧ Stored "cut.threshold" threshold σ ∧
    Prefix (RamUnsignedBuffer.encode (List.ofFn potential)) "cut.potential" σ

def compare (reversed : Bool) : Com :=
  if reversed then RamScalarComparison.command "cut.threshold" "cut.value"
  else RamScalarComparison.command "cut.value" "cut.threshold"
def emit : Com := .seq (.assign "rat.s" (.lit 0))
  (.seq (.assign "rat.n" (.var "cmp.le")) (.assign "rat.d" (.lit 1)))
def entry (reversed : Bool) : Com := .seq (RamArrayScalar.command "cut.potential" "cut.i" "cut.value")
  (.seq (compare reversed) emit)
def command (reversed : Bool) : Com := .seq (.assign "cut.pos" (.lit 0))
  (RamUnsignedVector.command "cut.i" "metric.n" "cut.flags" "cut.pos" (entry reversed))

theorem emit_spec (B : ℕ) (b : Bool) (h1 : 1<B) :
    Spec B (fun σ => σ.vars "cmp.le"=if b then 1 else 0) emit
      (fun _ τ => FractionOutput (bit b : ℚ) τ) 6 := by
  cases b <;> intro σ hσ <;> run_vcg
  all_goals simp_all [FractionOutput,fractionValue,bit] <;> omega

theorem compare_spec (B M : ℕ) (reversed : Bool) (a threshold : ℚ≥0) (hB : 2*M^2+3<B)
    (han : a.num≤M) (had : a.den≤M) (htn : threshold.num≤M) (htd : threshold.den≤M) :
    Spec B (fun σ => Stored "cut.value" a σ ∧ Stored "cut.threshold" threshold σ) (compare reversed)
      (fun _ τ => τ.vars "cmp.le"=if chosen reversed a threshold then 1 else 0) 64 := by
  cases reversed
  · simpa only [compare,Bool.false_eq_true,if_false,chosen,decide_eq_true_eq] using
      RamScalarComparison.command_spec B M a threshold "cut.value" "cut.threshold" hB han had htn htd (by decide) (by decide) (by decide)
  · intro σ hσ
    obtain ⟨τ,rr,pr⟩ := RamScalarComparison.command_spec B M threshold a "cut.threshold" "cut.value" hB htn htd han had
      (by decide) (by decide) (by decide) σ ⟨hσ.2,hσ.1⟩
    exact ⟨τ,rr,by simpa only [chosen,if_true,decide_eq_true_eq] using pr⟩

theorem entry_spec (B M : ℕ) {n : ℕ} (reversed : Bool) (potential : Fin n → ℚ≥0) (threshold : ℚ≥0)
    (v : Fin n) (hB : 2*M^2+3<B) (hindex : 2*n+2<B)
    (hpn : ∀ v, (potential v).num≤M) (hpd : ∀ v, (potential v).den≤M)
    (htn : threshold.num≤M) (htd : threshold.den≤M) :
    Spec B (fun σ => Context potential threshold σ ∧ σ.vars "cut.i"=v.val) (entry reversed)
      (fun _ τ => Context potential threshold τ ∧ FractionOutput (bit (chosen reversed (potential v) threshold) : ℚ) τ) 88 := by
  have hMB : M<B := by nlinarith
  rintro σ ⟨hσ,hidx⟩
  have hi : v.val<(List.ofFn potential).length := by simpa only [List.length_ofFn] using v.isLt
  have he : (List.ofFn potential)[v.val]=potential v := by simp
  obtain ⟨ν,rr,pr⟩ := RamArrayScalar.command_spec B "cut.potential" "cut.i" "cut.value" (List.ofFn potential) v.val hi
    (by nlinarith) (by omega) (by rw [he]; exact (hpn v).trans_lt hMB) (by rw [he]; exact (hpd v).trans_lt hMB)
    (by decide) (by decide) σ ⟨hσ.2.2,hidx⟩
  obtain ⟨μ,rc,pc⟩ := compare_spec B M reversed (potential v) threshold hB (hpn v) (hpd v) htn htd ν
    ⟨by simpa only [he] using pr,
      RamRoundingConstants.storedFrame rr hσ.2.1 (by decide) (by decide)⟩
  obtain ⟨τ,re,pe⟩ := emit_spec B (chosen reversed (potential v) threshold) (by nlinarith) μ pc
  have run := rr.seq (rc.seq re)
  refine ⟨τ,run,?_,pe⟩
  exact ⟨(run.frame_var _ (by cases reversed <;> decide)).trans hσ.1,
    RamRoundingConstants.storedFrame run hσ.2.1 (by cases reversed <;> decide) (by cases reversed <;> decide),
    by simpa only [Prefix,run.frame_arr "cut.potential" (by cases reversed <;> decide)] using hσ.2.2⟩

set_option maxHeartbeats 2400000 in
/-- Produce a non-strict threshold shore, or the reversed shore for a
negative potential, from the actual runtime potential buffer. -/
theorem command_spec (B M : ℕ) {n : ℕ} (reversed : Bool) (potential : Fin n → ℚ≥0) (threshold : ℚ≥0)
    (hB : 2*M^2+3<B) (hindex : 2*n+2<B)
    (hpn : ∀ v, (potential v).num≤M) (hpd : ∀ v, (potential v).den≤M)
    (htn : threshold.num≤M) (htd : threshold.den≤M) :
    Spec B (fun σ => Context potential threshold σ ∧ 2*n<(σ.arrs "cut.flags").length) (command reversed)
      (fun _ τ => Context potential threshold τ ∧ Prefix (RamUnsignedBuffer.encode
        (MaskedMassData.flags (fun v => chosen reversed (potential v) threshold))) "cut.flags" τ) (110*n+8) := by
  let qs := MaskedMassData.flags (fun v => chosen reversed (potential v) threshold)
  have hlen : qs.length=n := List.length_ofFn
  have hv : ∀ i, ∀ hi : i<qs.length, qs[i]=bit (chosen reversed (potential ⟨i,by simpa only [hlen] using hi⟩) threshold) := by
    intro i hi; simp [qs,MaskedMassData.flags,bit]
  have hwords : ∀ i, ∀ hi : i<qs.length, qs[i].num<B ∧ qs[i].den<B := by
    intro i hi; rw [hv i hi]
    cases chosen reversed (potential _) threshold <;> simp [bit] <;> omega
  have body : ∀ i, ∀ hi : i<qs.length,
      Spec B (fun σ => Context potential threshold σ ∧ σ.vars "cut.i"=i) (entry reversed)
        (fun _ τ => Context potential threshold τ ∧ FractionOutput (qs[i] : ℚ) τ) 88 := by
    intro i hi
    simpa only [hv i hi] using entry_spec B M reversed potential threshold ⟨i,by simpa only [hlen] using hi⟩ hB hindex hpn hpd htn htd
  have hf := RamUnsignedVector.command_spec B 88 (Context potential threshold) "cut.i" "metric.n" "cut.flags" "cut.pos" qs []
    (entry reversed) (by nlinarith) (by simp only [List.length_nil,hlen]; omega)
    (fun i hi => (hwords i hi).1) (fun i hi => (hwords i hi).2) (fun _ h => by simpa only [hlen] using h.1)
    (fun σ k h => by simpa only [Context,Stored,Prefix,vars_setVar,arrs_setVar,String.reduceAppend,String.reduceEq,if_false] using h)
    body (by cases reversed <;> decide) (by cases reversed <;> decide) (by cases reversed <;> decide)
    (by dsimp [RamUnsignedEncoding.command,RamWordBuffer.append,Com.wvars]; decide)
    (fun rr h => by
      simpa only [Context,Stored,Prefix,String.reduceAppend,
        rr.frame_var "metric.n" (by decide),rr.frame_var "cut.threshold.n" (by decide),rr.frame_var "cut.threshold.d" (by decide),
        rr.frame_arr "cut.potential" (by decide)] using h)
    (by decide) (by decide)
  rintro σ ⟨hσ,hroom⟩
  let ν := σ.setVar "cut.pos" 0
  have rz : Run B (.assign "cut.pos" (.lit 0)) σ ν 2 := Run.assign (evalB_lit (by nlinarith))
  obtain ⟨τ,rr,pr⟩ := hf ν ⟨by simpa only [Context,Stored,Prefix,ν,vars_setVar,arrs_setVar,String.reduceAppend,String.reduceEq,if_false] using hσ,
    by intro i hi; simp at hi,by simp [ν],by simpa only [ν,arrs_setVar,List.length_nil,Nat.zero_add,hlen] using hroom⟩
  exact ⟨τ,(rz.seq rr).mono (by simp only [hlen]; omega),pr.1,by simpa only [List.nil_append,qs] using pr.2.1⟩

end Lax455465Proofs.RamThresholdMask
