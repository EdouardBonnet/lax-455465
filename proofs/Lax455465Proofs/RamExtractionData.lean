import Lax455465Proofs.RamCommodityLoop
import Lax455465Proofs.FlowLpIndices

namespace Lax455465Proofs.RamExtractionData
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState
open LayeredFlowLP LayeredPathSweep
open scoped NNRat

structure Data {n L : ℕ} (q : Coordinate n L → ℚ≥0) (σ : Env) : Prop where
  order : σ.vars "lp.n"=n
  square : σ.vars "lp.n2"=n*n
  layer : σ.vars "short.layer"=L
  layerArcs : σ.vars "short.layerArcs"=L*(n*n)
  columns : σ.vars "lp.columns"=1+(n*n)*(L*(n*n))
  buffer : Prefix (RamUnsignedBuffer.encode (List.ofFn q)) "flow.primal" σ
  rawRoom : L+1<(σ.arrs "short.raw").length
  simpleRoom : L+1<(σ.arrs "short.simple").length

def names : List String := ["lp.n","lp.n2","short.layer","short.layerArcs","lp.columns"]

theorem to_path {n L : ℕ} {q : Coordinate n L → ℚ≥0} {σ : Env} (hd : Data q σ)
    (st : Edge n) (hc : σ.vars "short.commodity"=(DirectedFlowLP.edgeIndex n st).val)
    (hs : σ.vars "short.source"=st.1.val) : RamPathState.Data q st σ :=
  ⟨hd.order,hd.square,hd.layer,hd.layerArcs,hc,hs,hd.buffer,hd.rawRoom,hd.simpleRoom⟩

theorem of_path {n L : ℕ} {q : Coordinate n L → ℚ≥0} {st : Edge n} {σ : Env}
    (hd : RamPathState.Data q st σ) (hc : σ.vars "lp.columns"=1+(n*n)*(L*(n*n))) : Data q σ :=
  ⟨hd.order,hd.square,hd.layer,hd.layerArcs,hc,hd.buffer,hd.rawRoom,hd.simpleRoom⟩

theorem frame {B K : ℕ} {c : Com} {σ τ : Env} (rr : Run B c σ τ K)
    {n L : ℕ} {q : Coordinate n L → ℚ≥0} (h : Data q σ)
    (hx : ∀ x∈names,x∉c.wvars) (ha : "flow.primal"∉c.warrs) : Data q τ := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (rr.frame_var _ (hx _ (by simp [names]))).trans h.order
  · exact (rr.frame_var _ (hx _ (by simp [names]))).trans h.square
  · exact (rr.frame_var _ (hx _ (by simp [names]))).trans h.layer
  · exact (rr.frame_var _ (hx _ (by simp [names]))).trans h.layerArcs
  · exact (rr.frame_var _ (hx _ (by simp [names]))).trans h.columns
  · simpa only [Prefix,rr.frame_arr "flow.primal" ha] using h.buffer
  · simpa only [RamFrames.run_array_length rr "short.raw"] using h.rawRoom
  · simpa only [RamFrames.run_array_length rr "short.simple"] using h.simpleRoom

theorem set_index {n L : ℕ} {q : Coordinate n L → ℚ≥0} {σ : Env} (h : Data q σ) (i : ℕ) :
    Data q (σ.setVar "short.commodity" i) := by
  exact ⟨by simpa using h.order,by simpa using h.square,by simpa using h.layer,
    by simpa using h.layerArcs,by simpa using h.columns,h.buffer,h.rawRoom,h.simpleRoom⟩

def endpoints : Com := .seq (.assign "short.source" (.div (.var "short.commodity") (.var "lp.n")))
  (.assign "short.target" (.sub (.var "short.commodity") (.mul (.var "short.source") (.var "lp.n"))))

theorem endpoints_spec (B : ℕ) {n L : ℕ} (q : Coordinate n L → ℚ≥0) (st : Edge n)
    (hn : 0<n) (hsize : n+n*n<B) :
    Spec B (fun σ => Data q σ ∧ σ.vars "short.commodity"=(DirectedFlowLP.edgeIndex n st).val) endpoints
      (fun _ τ => Data q τ ∧ τ.vars "short.commodity"=(DirectedFlowLP.edgeIndex n st).val ∧
        τ.vars "short.source"=st.1.val ∧ τ.vars "short.target"=st.2.val) 10 := by
  rintro σ ⟨hd,hc⟩
  have hnσ:=hd.order
  have hnB : n<B := by omega
  have hsB : st.1.val<B := st.1.isLt.trans hnB
  have htB : st.2.val<B := st.2.isLt.trans hnB
  have hcB : (DirectedFlowLP.edgeIndex n st).val<B := (DirectedFlowLP.edgeIndex n st).isLt.trans (by omega)
  have hdiv := FlowLpIndices.edge_div st.1 st.2
  have hmod := FlowLpIndices.edge_mod st.1 st.2
  have hprod : st.1.val*n<B := by
    simpa only [hdiv] using (Nat.div_mul_le_self (DirectedFlowLP.edgeIndex n st).val n).trans_lt hcB
  let ν := (σ.setVar "short.source" st.1.val).setVar "short.target" st.2.val
  have rr : Run B endpoints σ ν 10 := by
    suffices ∃ τ,Run B endpoints σ τ 10 ∧ τ=ν by obtain ⟨τ,rr,rfl⟩:=this; exact rr
    unfold endpoints
    run_vcg
    all_goals simp_all [ν,Nat.mod_def,Nat.mul_comm]
  exact ⟨ν,rr,frame rr hd (by decide) (by decide),by simpa [ν] using hc,by simp [ν],by simp [ν]⟩

end Lax455465Proofs.RamExtractionData
