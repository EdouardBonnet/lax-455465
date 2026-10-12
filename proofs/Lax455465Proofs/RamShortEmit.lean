import Lax455465Proofs.RamShortHeader
import Lax455465Proofs.PathRecordBuffer
import Lax455465Proofs.RamEmitWords

namespace Lax455465Proofs.RamShortEmit
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState
open Lax455465.RationalEncoding RamExtractionStep PathRecordBuffer
open scoped NNRat

def command : Com := .seq (.store "short.output" (.lit 2) (.var "short.recordCount"))
  (.seq (.assign "emit.count" (.var "short.outputLength")) (RamEmitWords.command "short.output" 1))

theorem patched {n : ℕ} (f : ℚ≥0) (rs : PathRecordBuffer.Records n) (σ : Env)
    (hp : Prefix (RamShortHeader.header f++encode rs) "short.output" σ) :
    Prefix (encodeFlow ⟨f,rs⟩) "short.output" (σ.setArr "short.output" 2 rs.length) := by
  intro i hi
  have hlen : (encodeFlow ⟨f,rs⟩).length=(RamShortHeader.header f++encode rs).length := by
    simp [encodeFlow,RamShortHeader.header,encode,RamPathRecord.encode,RamPathState.simple,encodeRational]
  have hold : i<(RamShortHeader.header f++encode rs).length := by omega
  by_cases he : i=2
  · subst i
    have hroom : 2<(σ.arrs "short.output").length := by
      by_contra hh
      have hz:=hp 2 hold
      rw [List.getElem?_eq_none (by omega)] at hz
      cases hz
    simp [arrs_setArr,List.getElem?_set_self hroom,encodeFlow,encodeRational]
  · have hh:=hp i hold
    have hv : (RamShortHeader.header f++encode rs)[i]=(encodeFlow ⟨f,rs⟩)[i] := by
      have hpre : encodeFlow ⟨f,rs⟩=(RamShortHeader.header f++encode rs).set 2 rs.length := by
        simp [encodeFlow,RamShortHeader.header,encode,RamPathRecord.encode,RamPathState.simple,encodeRational]
      simp only [hpre,List.getElem_set_ne (Ne.symm he)]
    simpa only [arrs_setArr,if_true,List.getElem?_set_ne (Ne.symm he),hv] using hh

/-- Patch the actual record count and emit the exact public flow encoding. -/
theorem command_spec (B : ℕ) {n : ℕ} (f : ℚ≥0) (rs : PathRecordBuffer.Records n)
    (hB : 3<B) (hlen : (encodeFlow ⟨f,rs⟩).length<B)
    (hwords : ∀ x∈encodeFlow ⟨f,rs⟩,x<B) :
    Spec B (fun σ => Output (RamShortHeader.header f++encode rs) rs.length σ ∧ σ.out=[]) command
      (fun _ τ => τ.out=encodeFlow ⟨f,rs⟩) (13*(encodeFlow ⟨f,rs⟩).length+11) := by
  rintro σ ⟨ho,hout⟩
  have hc : rs.length<B := hwords _ (by simp [encodeFlow])
  have hroom : 2<(σ.arrs "short.output").length := by
    have hi : 2<(RamShortHeader.header f++encode rs).length := by simp [RamShortHeader.header,encodeRational] <;> omega
    by_contra hh
    have hz:=ho.buffer 2 hi
    rw [List.getElem?_eq_none (by omega)] at hz
    cases hz
  let ν:=σ.setArr "short.output" 2 rs.length
  have r1 : Run B (.store "short.output" (.lit 2) (.var "short.recordCount")) σ ν 3 :=
    Run.store (evalB_lit (by omega)) (by rw [evalB_var_iff]; exact ⟨ho.count.symm,ho.count ▸ hc⟩) hroom
  have hpν:=patched f rs σ ho.buffer
  have he : (RamShortHeader.header f++encode rs).length=(encodeFlow ⟨f,rs⟩).length := by
    simp [RamShortHeader.header,encodeFlow,encode,RamPathRecord.encode,RamPathState.simple,encodeRational]
  have hposν : ν.vars "short.outputLength"=(encodeFlow ⟨f,rs⟩).length := ho.cursor.trans he
  let μ:=ν.setVar "emit.count" (encodeFlow ⟨f,rs⟩).length
  have r2 : Run B (.assign "emit.count" (.var "short.outputLength")) ν μ 2 :=
    Run.assign (by rw [evalB_var_iff]; exact ⟨hposν.symm,hposν ▸ hlen⟩)
  obtain ⟨τ,r3,p3⟩ := RamEmitWords.command_spec B "short.output" 1 (encodeFlow ⟨f,rs⟩) []
    (by omega) (by omega) (by simpa using hlen) hlen hwords μ
    ⟨by intro i hi; simpa only [RamEmitWords.Data,Nat.one_mul,μ,arrs_setVar] using hpν i hi,
      by simp [μ],hout⟩
  exact ⟨τ,(r1.seq (r2.seq r3)).mono (by omega),by simpa using p3⟩

end Lax455465Proofs.RamShortEmit
