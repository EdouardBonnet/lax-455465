import Lax455465Proofs.RamPathState

namespace Lax455465Proofs.RamPathInit
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState
open LayeredFlowLP LayeredGraphFlow LayeredWalkState RamPathState
open scoped NNRat

def command : Com := .seq (.assign "short.rawLength" (.lit 0))
  (.seq (.assign "short.simpleLength" (.lit 0))
  (.seq (.assign "short.vertex" (.var "short.source"))
  (.seq (RamWordBuffer.append "short.raw" "short.rawLength" (.var "short.vertex"))
  (.seq RamCycleAppend.command (.assign "short.level" (.lit 0))))))

theorem command_spec (B : ℕ) {n L : ℕ} (qs : Fin (1+(n*n)*(L*(n*n))) → ℚ≥0)
    (st : Edge n) (hn : n<B) (h1 : 1<B) :
    Spec B (Data qs st) command
      (fun _ τ => Data qs st τ ∧ Buffers (L := L) [(0,st.1)] (0,st.1) [st.1] τ) 60 := by
  intro σ hd
  let σ1 := σ.setVar "short.rawLength" 0
  have r1 : Run B (.assign "short.rawLength" (.lit 0)) σ σ1 2 := Run.assign (evalB_lit (by omega))
  let σ2 := σ1.setVar "short.simpleLength" 0
  have r2 : Run B (.assign "short.simpleLength" (.lit 0)) σ1 σ2 2 := Run.assign (evalB_lit (by omega))
  have hd2 := data_frame (r1.seq r2) hd (by decide) (by decide)
  let σ3 := σ2.setVar "short.vertex" st.1.val
  have r3 : Run B (.assign "short.vertex" (.var "short.source")) σ2 σ3 2 :=
    Run.assign (by rw [evalB_var_iff]; exact ⟨hd2.source.symm,hd2.source ▸ st.1.isLt.trans hn⟩)
  have hd3 := data_frame r3 hd2 (by decide) (by decide)
  have hv3 : σ3.vars "short.vertex"=st.1.val := by simp [σ3]
  obtain ⟨σ4,r4,p4⟩ := RamWordBuffer.append_spec B "short.raw" "short.rawLength" [] st.1.val (.var "short.vertex")
    h1 (by simpa using h1) σ3
    ⟨by intro i hi; simp at hi,by simp [σ3,σ2,σ1],by have hh := hd3.rawRoom; simp only [List.length_nil]; omega,
      by rw [evalB_var_iff]; exact ⟨hv3.symm,hv3 ▸ st.1.isLt.trans hn⟩⟩
  have hd4 := data_frame r4 hd3 (by decide) (by decide)
  have hsl4 : σ4.vars "short.simpleLength"=0 := (r4.frame_var _ (by decide)).trans (by simp [σ3,σ2])
  have hv4 := (r4.frame_var "short.vertex" (by decide)).trans hv3
  obtain ⟨σ5,r5,p5⟩ := RamCycleAppend.command_spec B [] st.1.val (by simp) (by simpa using h1)
    (st.1.isLt.trans hn) (by simp) h1 σ4
    ⟨by intro i hi; simp at hi,by simpa using hsl4,hv4,by have hh := hd4.simpleRoom; simp only [List.length_nil]; omega⟩
  have hd5 := data_frame r5 hd4 (by decide) (by decide)
  let τ := σ5.setVar "short.level" 0
  have r6 : Run B (.assign "short.level" (.lit 0)) σ5 τ 2 := Run.assign (evalB_lit (by omega))
  have tail := r5.seq r6
  refine ⟨τ,(r1.seq (r2.seq (r3.seq (r4.seq tail)))).mono (by simp [Expr.size]),
    data_frame r6 hd5 (by decide) (by decide),?_,?_,?_,?_,?_,?_⟩
  · simpa only [vertices,List.map_cons,List.map_nil,List.nil_append,Prefix,tail.frame_arr "short.raw" (by decide)] using p4.1
  · simpa only [List.length_cons,List.length_nil,Nat.zero_add,tail.frame_var "short.rawLength" (by decide)] using p4.2
  · simpa [simple,LoopErasure.append,Prefix,τ,arrs_setVar] using p5.1
  · simpa [LoopErasure.append,τ] using p5.2
  · simpa only [tail.frame_var "short.vertex" (by decide)] using hv4
  · simp [τ]

end Lax455465Proofs.RamPathInit
