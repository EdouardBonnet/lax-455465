import Lax455465Proofs.RamWordVectorAppend
import Lax455465Proofs.RamUnsignedEncoding
import Lax455465Proofs.RamUnsignedScalar

namespace Lax455465Proofs.RamPathRecord
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamRational
open scoped NNRat

def encode (xs : List ℕ) (w : ℚ≥0) : List ℕ := [xs.length]++xs++Lax455465.RationalEncoding.encodeRational w

def command : Com := .seq (RamWordBuffer.append "short.output" "short.outputLength" (.var "short.simpleLength"))
  (.seq RamWordVectorAppend.command (.seq (RamUnsignedScalar.load "short.amount")
  (.seq (RamUnsignedEncoding.command "short.output" "short.outputLength")
    (.assign "short.recordCount" (.add (.var "short.recordCount") (.lit 1))))))

/-- Emit the actual simple path and its canonical rational bottleneck
amount, then count this record for the final certificate header. -/
theorem command_spec (B : ℕ) (front xs : List ℕ) (w : ℚ≥0) (count : ℕ)
    (h1 : 1<B) (hlen : front.length+xs.length+4<B) (hc : count+1<B)
    (hn : w.num<B) (hd : w.den<B) (hwords : ∀ x∈xs,x<B) :
    Spec B (fun σ => Prefix front "short.output" σ ∧ σ.vars "short.outputLength"=front.length ∧
      Prefix xs "short.simple" σ ∧ σ.vars "short.simpleLength"=xs.length ∧
      RamUnsignedScalar.Stored "short.amount" w σ ∧ σ.vars "short.recordCount"=count ∧
      front.length+xs.length+3<(σ.arrs "short.output").length) command
      (fun _ τ => Prefix (front++encode xs w) "short.output" τ ∧
        τ.vars "short.outputLength"=front.length+xs.length+3 ∧ τ.vars "short.recordCount"=count+1)
      (16*xs.length+50) := by
  rintro σ ⟨hp,hpos,hxs,hsize,hw,hcount,hroom⟩
  obtain ⟨s1,r1,p1⟩ := RamWordBuffer.append_spec B "short.output" "short.outputLength" front xs.length
    (.var "short.simpleLength") h1 (by omega) σ
    ⟨hp,hpos,by omega,by rw [evalB_var_iff]; exact ⟨hsize.symm,hsize ▸ (by omega : xs.length<B)⟩⟩
  let header := front++[xs.length]
  have hh : header.length=front.length+1 := by simp [header]
  have hxs1 : Prefix xs "short.simple" s1 := by
    simpa only [Prefix,r1.frame_arr "short.simple" (by decide)] using hxs
  have hsize1 := (r1.frame_var "short.simpleLength" (by decide)).trans hsize
  have hroom1 : front.length+xs.length+3<(s1.arrs "short.output").length := by
    simpa only [RamFrames.run_array_length r1 "short.output"] using hroom
  obtain ⟨s2,r2,p2⟩ := RamWordVectorAppend.command_spec B header xs h1 (by rw [hh]; omega) hwords s1
    ⟨hxs1,hsize1,p1.1,by simpa only [hh] using p1.2,by rw [hh]; omega⟩
  have hw2 : RamUnsignedScalar.Stored "short.amount" w s2 := by
    simpa only [RamUnsignedScalar.Stored,String.reduceAppend,(r1.seq r2).frame_var "short.amount.n" (by decide),
      (r1.seq r2).frame_var "short.amount.d" (by decide)] using hw
  obtain ⟨s3,r3,p3⟩ := RamUnsignedScalar.load_spec B "short.amount" w h1 hn hd (by decide) s2 hw2
  let words := header++xs
  have hwordsLen : words.length=front.length+xs.length+1 := by simp [words,hh]; omega
  have hprefix3 : Prefix words "short.output" s3 := by
    simpa only [Prefix,r3.frame_arr "short.output" (by decide)] using p2.1
  have hpos3 : s3.vars "short.outputLength"=words.length := by
    simpa only [r3.frame_var "short.outputLength" (by decide),words,List.length_append] using p2.2
  have hroom3 : words.length+1<(s3.arrs "short.output").length := by
    rw [hwordsLen,RamFrames.run_array_length r3 "short.output",RamFrames.run_array_length r2 "short.output"]
    omega
  obtain ⟨s4,r4,p4⟩ := RamUnsignedEncoding.command_spec B "short.output" "short.outputLength" w words h1 hn hd
    (by rw [hwordsLen]; omega) (by decide) s3 ⟨p3,hprefix3,hpos3,hroom3⟩
  have before := r1.seq (r2.seq (r3.seq r4))
  have hc4 := (before.frame_var "short.recordCount" (by decide)).trans hcount
  let τ := s4.setVar "short.recordCount" (count+1)
  have r5 : Run B (.assign "short.recordCount" (.add (.var "short.recordCount") (.lit 1))) s4 τ 4 :=
    Run.assign (evalB_bin (op := .add)
      (by rw [evalB_var_iff]; exact ⟨hc4.symm,hc4 ▸ (by omega : count<B)⟩)
      (evalB_lit h1) hc)
  refine ⟨τ,(r1.seq (r2.seq (r3.seq (r4.seq r5)))).mono (by simp only [Expr.size]; omega),?_,?_,by simp [τ]⟩
  · simpa only [encode,words,header,List.append_assoc,Prefix,τ,arrs_setVar] using p4.1
  · simpa only [τ,vars_setVar,String.reduceEq,if_false,hwordsLen,Nat.add_assoc] using p4.2

end Lax455465Proofs.RamPathRecord
