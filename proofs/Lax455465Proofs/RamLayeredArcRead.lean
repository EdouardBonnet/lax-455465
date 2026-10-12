import Lax455465Proofs.LayeredArcIndex
import Lax455465Proofs.RamUnsignedBuffer

namespace Lax455465Proofs.RamLayeredArcRead
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamVirtualState LayeredFlowLP
open scoped NNRat

def command : Com := .seq
  (.assign "short.arcIndex" (.add (.add (.add (.add (.lit 1)
    (.mul (.var "short.commodity") (.var "short.layerArcs")))
    (.mul (.var "short.level") (.var "lp.n2")))
    (.mul (.var "short.vertex") (.var "lp.n"))) (.var "find.i")))
  (RamUnsignedBuffer.read "flow.primal" "short.arcIndex")

structure Context {n L : ℕ} (qs : Fin (1+(n*n)*(L*(n*n))) → ℚ≥0)
    (st : Edge n) (k : Fin L) (u v : Fin n) (σ : Env) : Prop where
  order : σ.vars "lp.n"=n
  square : σ.vars "lp.n2"=n*n
  layerArcs : σ.vars "short.layerArcs"=L*(n*n)
  commodity : σ.vars "short.commodity"=(DirectedFlowLP.edgeIndex n st).val
  level : σ.vars "short.level"=k.val
  vertex : σ.vars "short.vertex"=u.val
  choice : σ.vars "find.i"=v.val
  buffer : Prefix (RamUnsignedBuffer.encode (List.ofFn qs)) "flow.primal" σ

/-- Read one residual arc of the current commodity and layer directly
from the initialized primal buffer using the same typed LP index. -/
theorem index_spec (B : ℕ) {n L : ℕ} (qs : Fin (1+(n*n)*(L*(n*n))) → ℚ≥0)
    (st : Edge n) (k : Fin L) (u v : Fin n)
    (hsize : n+n*n+L*(n*n)+2*(1+(n*n)*(L*(n*n)))+4<B)
    (hnum : (qs (variableIndex n L (.inr (st,(k,(u,v)))))).num<B)
    (hden : (qs (variableIndex n L (.inr (st,(k,(u,v)))))).den<B) :
    Spec B (Context qs st k u v) command
      (fun _ τ => FractionOutput (qs (variableIndex n L (.inr (st,(k,(u,v))))) : ℚ) τ ∧
        τ.vars "short.arcIndex"=(variableIndex n L (.inr (st,(k,(u,v))))).val) 40 := by
  let j := (variableIndex n L (.inr (st,(k,(u,v))))).val
  have hj := LayeredArcIndex.value st k u v
  have hjBound := (variableIndex n L (.inr (st,(k,(u,v))))).isLt
  have he : j=1+(DirectedFlowLP.edgeIndex n st).val*(L*(n*n))+k.val*(n*n)+u.val*n+v.val := hj
  have hst := (DirectedFlowLP.edgeIndex n st).isLt
  have hsmall : n<B ∧ n*n<B ∧ L*(n*n)<B ∧
      (DirectedFlowLP.edgeIndex n st).val<B ∧ k.val<B ∧ u.val<B ∧ v.val<B ∧
      (DirectedFlowLP.edgeIndex n st).val*(L*(n*n))<B ∧ k.val*(n*n)<B ∧ u.val*n<B ∧ j+1<B := by
    have hLpos : 0<L := Nat.zero_lt_of_lt k.isLt
    have hnPos : 0<n := Nat.zero_lt_of_lt u.isLt
    have hL : L≤L*(n*n) := by nlinarith
    omega
  rintro σ hctx
  let ν := σ.setVar "short.arcIndex" j
  have rindex : Run B (.assign "short.arcIndex" (.add (.add (.add (.add (.lit 1)
      (.mul (.var "short.commodity") (.var "short.layerArcs")))
      (.mul (.var "short.level") (.var "lp.n2")))
      (.mul (.var "short.vertex") (.var "lp.n"))) (.var "find.i"))) σ ν 18 := by
    rcases hctx with ⟨hn,hn2,hA,hstσ,hkσ,huσ,hvσ,hbuffer⟩
    suffices ∃ τ,Run B (.assign "short.arcIndex" (.add (.add (.add (.add (.lit 1)
        (.mul (.var "short.commodity") (.var "short.layerArcs")))
        (.mul (.var "short.level") (.var "lp.n2")))
        (.mul (.var "short.vertex") (.var "lp.n"))) (.var "find.i"))) σ τ 18 ∧ τ=ν by
      obtain ⟨τ,hr,rfl⟩ := this
      exact hr
    run_vcg
    all_goals simp_all [ν,LayeredArcIndex.index]
    all_goals omega
  obtain ⟨τ,rr,pr⟩ := RamUnsignedBuffer.read_spec B "flow.primal" "short.arcIndex" (List.ofFn qs) j
    (by simpa only [List.length_ofFn] using hjBound) (by omega) (by omega)
    (by simpa only [List.getElem_ofFn,Fin.eta] using hnum)
    (by simpa only [List.getElem_ofFn,Fin.eta] using hden) (by decide) ν
    ⟨by simpa only [ν,Prefix,arrs_setVar] using hctx.buffer,by simp [ν]⟩
  exact ⟨τ,(rindex.seq rr).mono (by omega),(by simpa only [List.getElem_ofFn,Fin.eta] using pr.1),
    (rr.frame_var "short.arcIndex" (by decide)).trans (by simp [ν,j])⟩

theorem command_spec (B : ℕ) {n L : ℕ} (qs : Fin (1+(n*n)*(L*(n*n))) → ℚ≥0)
    (st : Edge n) (k : Fin L) (u v : Fin n)
    (hsize : n+n*n+L*(n*n)+2*(1+(n*n)*(L*(n*n)))+4<B)
    (hnum : (qs (variableIndex n L (.inr (st,(k,(u,v)))))).num<B)
    (hden : (qs (variableIndex n L (.inr (st,(k,(u,v)))))).den<B) :
    Spec B (Context qs st k u v) command
      (fun _ τ => FractionOutput (qs (variableIndex n L (.inr (st,(k,(u,v))))) : ℚ) τ) 40 := by
  intro σ hσ
  obtain ⟨τ,rr,pr⟩ := index_spec B qs st k u v hsize hnum hden σ hσ
  exact ⟨τ,rr,pr.1⟩

end Lax455465Proofs.RamLayeredArcRead
