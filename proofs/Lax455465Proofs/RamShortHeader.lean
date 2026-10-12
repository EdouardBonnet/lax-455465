import Lax455465Proofs.RamExtractionStep
import Lax455465Proofs.RamHalfFraction

namespace Lax455465Proofs.RamShortHeader
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamRational
open Lax455465.RationalEncoding RamExtractionStep
open scoped NNRat

def header (f : ℚ≥0) : List ℕ := encodeRational f++[0]

def writeHeader : Com := .seq (.assign "short.outputLength" (.lit 0))
  (.seq (RamUnsignedEncoding.command "short.output" "short.outputLength")
    (.seq (RamWordBuffer.append "short.output" "short.outputLength" (.lit 0))
      (.assign "short.recordCount" (.lit 0))))

def command : Com := .seq (RamUnsignedScalar.save "short.value")
  (.seq writeHeader (.seq RamHalfFraction.command (RamUnsignedScalar.save "short.initial")))

theorem half_height (M : ℕ) (f : ℚ≥0) (hf : LpInputSize.Height M (f : ℚ)) :
    LpInputSize.Height (2*M) ((f/2 : ℚ≥0) : ℚ) := by
  have hh := LpInputSize.height_mul hf (show LpInputSize.Height 2 (1/2 : ℚ) by norm_num [LpInputSize.Height])
  simpa [NNRat.coe_div,div_eq_mul_inv,Nat.mul_comm] using hh

theorem write_spec (B : ℕ) (f : ℚ≥0) (hB : 4<B) (hn : f.num<B) (hd : f.den<B) :
    Spec B (fun σ => FractionOutput (f : ℚ) σ ∧ 3<(σ.arrs "short.output").length) writeHeader
      (fun _ τ => Output (header f) 0 τ) 25 := by
  rintro σ ⟨hf,hroom⟩
  let ν:=σ.setVar "short.outputLength" 0
  have r1 : Run B (.assign "short.outputLength" (.lit 0)) σ ν 2 := Run.assign (evalB_lit (by omega))
  have hfν : FractionOutput (f : ℚ) ν := by simpa [ν,FractionOutput] using hf
  obtain ⟨μ,r2,p2⟩ := RamUnsignedEncoding.command_spec B "short.output" "short.outputLength" f [] (by omega)
    hn hd (by simp; omega) (by decide) ν ⟨hfν,by simp [Prefix],by simp [ν],by simp only [List.length_nil]; exact hroom.trans' (by omega)⟩
  have hlen : (encodeRational f).length=2 := rfl
  obtain ⟨ρ,r3,p3⟩ := RamWordBuffer.append_spec B "short.output" "short.outputLength" (encodeRational f) 0 (.lit 0)
    (by omega) (by rw [hlen]; omega) μ ⟨by simpa using p2.1,by simpa only [hlen,List.length_nil,Nat.zero_add] using p2.2,
      by rw [hlen,RamFrames.run_array_length r2 "short.output"]; exact hroom.trans' (by omega),evalB_lit (by omega)⟩
  let τ:=ρ.setVar "short.recordCount" 0
  have r4 : Run B (.assign "short.recordCount" (.lit 0)) ρ τ 2 := Run.assign (evalB_lit (by omega))
  refine ⟨τ,(r1.seq (r2.seq (r3.seq r4))).mono (by simp only [Expr.size]; omega),?_,?_,by simp [τ]⟩
  · simpa only [header,Prefix,τ,arrs_setVar] using p3.1
  · simpa only [header,List.length_append,List.length_singleton,hlen,τ,vars_setVar,String.reduceEq,if_false] using p3.2

/-- Initialize the exact certificate header and the common half-demand.
The record count is filled from the actual extraction loop at emission. -/
theorem command_spec (B M : ℕ) (f : ℚ≥0) (hB : 4<B) (hM : 2*M<B)
    (hf : LpInputSize.Height M (f : ℚ)) :
    Spec B (fun σ => FractionOutput (f : ℚ) σ ∧ σ.vars "rat.s"=0 ∧ 3<(σ.arrs "short.output").length)
      command (fun _ τ => Output (header f) 0 τ ∧ RamUnsignedScalar.Stored "short.initial" (f/2) τ ∧
        RamUnsignedScalar.Stored "short.value" f τ) (36*(2*M).size+53) := by
  have hn : f.num<B := by simpa only [NNRat.natAbs_num_coe] using hf.1.trans_lt (by omega : M<B)
  have hd : f.den<B := hf.2.trans_lt (by omega : M<B)
  rintro σ ⟨hfrac,hsgn,hroom⟩
  obtain ⟨s1,r1,p1⟩ := RamUnsignedScalar.save_spec B "short.value" f hn hd (by decide) σ hfrac
  have hf1 : FractionOutput (f : ℚ) s1 := by
    simpa only [FractionOutput,r1.frame_var "rat.n" (by decide),r1.frame_var "rat.d" (by decide),
      r1.frame_var "rat.s" (by decide)] using hfrac
  obtain ⟨s2,r2,p2⟩ := write_spec B f hB hn hd s1 ⟨hf1,by simpa only [RamFrames.run_array_length r1 "short.output"] using hroom⟩
  have hf2 : FractionOutput (f : ℚ) s2 := by
    simpa only [FractionOutput,r2.frame_var "rat.n" (by decide),r2.frame_var "rat.d" (by decide),
      r2.frame_var "rat.s" (by decide)] using hf1
  have hs2 := ((r1.seq r2).frame_var "rat.s" (by decide)).trans hsgn
  obtain ⟨s3,r3,p3⟩ := RamHalfFraction.command_spec B M f (by omega) hM hf s2 ⟨hf2,hs2⟩
  have hh := half_height M f hf
  obtain ⟨τ,r4,p4⟩ := RamUnsignedScalar.save_spec B "short.initial" (f/2)
    (by simpa only [NNRat.natAbs_num_coe] using hh.1.trans_lt hM) (hh.2.trans_lt hM) (by decide) s3 p3.1
  have hvτ : RamUnsignedScalar.Stored "short.value" f τ := by
    simpa only [RamUnsignedScalar.Stored,String.reduceAppend,
      (r2.seq (r3.seq r4)).frame_var "short.value.n" (by decide),
      (r2.seq (r3.seq r4)).frame_var "short.value.d" (by decide)] using p1
  exact ⟨τ,(r1.seq (r2.seq (r3.seq r4))).mono (by omega),
    output_frame (r3.seq r4) p2 (by decide) (by decide) (by decide),p4,hvτ⟩

end Lax455465Proofs.RamShortHeader
