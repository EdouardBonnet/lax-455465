import Lax455465Proofs.RamPathState
import Lax455465Proofs.LoopErasureMap

namespace Lax455465Proofs.RamPathExtend
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState
open LayeredFlowLP LayeredGraphFlow LayeredWalkState RamPathState
open scoped NNRat

/-- Extend the raw path by one positive residual edge and update the
simple physical stack by the same actual chosen vertex. -/
def command : Com := .seq (.assign "find.count" (.var "lp.n"))
  (.seq RamPositiveNext.command
  (.seq (.assign "short.vertex" (.var "find.result"))
  (.seq (RamWordBuffer.append "short.raw" "short.rawLength" (.var "short.vertex"))
  (.seq RamCycleAppend.command (.assign "short.level" (.add (.var "short.level") (.lit 1)))))))

theorem command_spec (B : ℕ) {n L : ℕ} (qs : Fin (1+(n*n)*(L*(n*n))) → ℚ≥0)
    (st : Edge n) (a : ℚ) (ha : 0<a)
    (hb : AcyclicFlowPath.Balance (graph (arc qs) st) (0,st.1) (Fin.last L,st.2) a)
    (hsize : n+n*n+L*(n*n)+2*(1+(n*n)*(L*(n*n)))+2*L+20<B)
    (hnum : ∀ j,(qs j).num<B) (hden : ∀ j,(qs j).den<B) :
    Spec B (fun σ => Invariant qs st σ ∧ σ.vars "short.level"<L) command
      (fun σ τ => Invariant qs st τ ∧ τ.vars "short.level"=σ.vars "short.level"+1)
      (100*n+100*L+200) := by
  rintro σ ⟨⟨hdata,xs,p,ys,hw,hbuf⟩,hlt⟩
  have hk : p.1.val<L := by rwa [hbuf.level] at hlt
  let k : Fin L := ⟨p.1.val,hk⟩
  have hnB : n<B := by omega
  have h1 : 1<B := by omega
  have hxlen : xs.length≤L := by rw [hw.length]; omega
  have hylen : ys.length≤L := hw.simpleLength.trans hxlen
  let σ1 := σ.setVar "find.count" n
  have r1 : Run B (.assign "find.count" (.var "lp.n")) σ σ1 2 :=
    Run.assign (by rw [evalB_var_iff]; exact ⟨hdata.order.symm,hdata.order ▸ hnB⟩)
  have hd1 := data_frame r1 hdata (by decide) (by decide)
  have hbuf1 := buffers_frame r1 hbuf (by decide) (by decide) (by decide)
  obtain ⟨σ2,r2,p2⟩ := RamPositiveNext.command_spec B qs st k p.2 (by omega)
    (fun v => hnum _) (fun v => hden _) (successor qs st hw hk a ha hb) σ1
    ⟨hd1.order,hd1.square,hd1.layerArcs,hd1.commodity,hbuf1.level,hbuf1.vertex,hd1.buffer,by simp [σ1]⟩
  obtain ⟨v,hfound,hvσ2,hv⟩ := p2.2
  have hd2 := data_frame r2 hd1 (by decide) (by decide)
  have hbuf2 := buffers_frame r2 hbuf1 (by decide) (by decide) (by decide)
  let σ3 := σ2.setVar "short.vertex" v.val
  have r3 : Run B (.assign "short.vertex" (.var "find.result")) σ2 σ3 2 :=
    Run.assign (by rw [evalB_var_iff]; exact ⟨hvσ2.symm,hvσ2 ▸ v.isLt.trans hnB⟩)
  have hd3 := data_frame r3 hd2 (by decide) (by decide)
  have hv3 : σ3.vars "short.vertex"=v.val := by simp [σ3]
  have hr3 : Prefix (vertices xs) "short.raw" σ3 := hbuf2.raw
  have hl3 : σ3.vars "short.rawLength"=(vertices xs).length := by simpa only [vertices,List.length_map,σ3,vars_setVar,String.reduceEq,if_false] using hbuf2.rawLength
  obtain ⟨σ4,r4,p4⟩ := RamWordBuffer.append_spec B "short.raw" "short.rawLength" (vertices xs) v.val (.var "short.vertex")
    h1 (by simp only [vertices,List.length_map]; omega) σ3
    ⟨hr3,hl3,by simpa only [vertices,List.length_map] using (hxlen.trans (Nat.le_succ L)).trans_lt hd3.rawRoom,
      by rw [evalB_var_iff]; exact ⟨hv3.symm,hv3 ▸ v.isLt.trans hnB⟩⟩
  have hd4 := data_frame r4 hd3 (by decide) (by decide)
  have hs4 : Prefix (simple ys) "short.simple" σ4 := by
    simpa only [Prefix,r4.frame_arr "short.simple" (by decide),σ3,arrs_setVar] using hbuf2.stack
  have hsl4 : σ4.vars "short.simpleLength"=(simple ys).length := by
    simpa only [simple,List.length_map,r4.frame_var "short.simpleLength" (by decide),σ3,vars_setVar,String.reduceEq,if_false] using hbuf2.stackLength
  have hv4 := (r4.frame_var "short.vertex" (by decide)).trans hv3
  obtain ⟨σ5,r5,p5⟩ := RamCycleAppend.command_spec B (simple ys) v.val (List.Nodup.map Fin.val_injective hw.simple)
    (by simp only [simple,List.length_map]; omega) (v.isLt.trans hnB)
    (by intro z hz; obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hz; exact u.isLt.trans hnB) h1 σ4
    ⟨hs4,hsl4,hv4,by simpa only [simple,List.length_map] using (hylen.trans (Nat.le_succ L)).trans_lt hd4.simpleRoom⟩
  have hd5 := data_frame r5 hd4 (by decide) (by decide)
  have pre := r1.seq (r2.seq (r3.seq (r4.seq r5)))
  have hlevel5 : σ5.vars "short.level"=p.1.val := (pre.frame_var "short.level" (by decide)).trans hbuf.level
  let τ := σ5.setVar "short.level" (p.1.val+1)
  have r6 : Run B (.assign "short.level" (.add (.var "short.level") (.lit 1))) σ5 τ 4 :=
    Run.assign (evalB_bin (op := .add)
      (by rw [evalB_var_iff]; exact ⟨hlevel5.symm,hlevel5 ▸ (by omega : p.1.val<B)⟩)
      (evalB_lit h1) (by dsimp [Bop.apply]; omega))
  let q : Vertex n L := (k.succ,v)
  have hwalk : Walk qs st (xs++[q]) q (LoopErasure.append ys v) := extend qs st hw hk v hv
  have heSimple : simple (LoopErasure.append ys v)=LoopErasure.append (simple ys) v.val :=
    LoopErasureMap.append Fin.val Fin.val_injective ys v
  have heRaw : vertices (xs++[q])=vertices xs++[v.val] := by simp [vertices,q]
  refine ⟨τ,(r1.seq (r2.seq (r3.seq (r4.seq (r5.seq r6))))).mono (by simp only [simple,List.length_map,Expr.size]; omega),?_,?_⟩
  · refine ⟨data_frame r6 hd5 (by decide) (by decide),xs++[q],q,LoopErasure.append ys v,hwalk,?_,?_,?_,?_,?_,?_⟩
    · rw [heRaw]
      simpa only [Prefix,τ,arrs_setVar,r5.frame_arr "short.raw" (by decide)] using p4.1
    · have he := (r5.frame_var "short.rawLength" (by decide)).trans p4.2
      simpa only [τ,vars_setVar,String.reduceEq,if_false,vertices,List.length_map,List.length_append,List.length_singleton] using he
    · rw [heSimple]
      exact p5.1
    · have hl : (LoopErasure.append (simple ys) v.val).length=(LoopErasure.append ys v).length := by
        rw [←heSimple]
        simp only [simple,List.length_map]
      simpa only [τ,vars_setVar,String.reduceEq,if_false,hl] using p5.2
    · have he := (r5.frame_var "short.vertex" (by decide)).trans hv4
      simpa only [τ,vars_setVar,String.reduceEq,if_false,q] using he
    · simp only [τ,vars_setVar,if_true,q]
      rfl
  · simp only [τ,vars_setVar,if_true,hbuf.level]

end Lax455465Proofs.RamPathExtend
