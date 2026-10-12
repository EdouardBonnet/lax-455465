import Lax455465Proofs.LayeredWalkState
import Lax455465Proofs.RamPositiveNext
import Lax455465Proofs.RamCycleAppend

namespace Lax455465Proofs.RamPathState
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState
open LayeredFlowLP LayeredGraphFlow LayeredWalkState
open scoped NNRat

def vertices {n L : ℕ} (xs : List (Vertex n L)) : List ℕ := xs.map (fun p => p.2.val)

def simple {n : ℕ} (ys : List (Fin n)) : List ℕ := ys.map Fin.val

structure Data {n L : ℕ} (qs : Fin (1+(n*n)*(L*(n*n))) → ℚ≥0) (st : Edge n) (σ : Env) : Prop where
  order : σ.vars "lp.n"=n
  square : σ.vars "lp.n2"=n*n
  layer : σ.vars "short.layer"=L
  layerArcs : σ.vars "short.layerArcs"=L*(n*n)
  commodity : σ.vars "short.commodity"=(DirectedFlowLP.edgeIndex n st).val
  source : σ.vars "short.source"=st.1.val
  buffer : Prefix (RamUnsignedBuffer.encode (List.ofFn qs)) "flow.primal" σ
  rawRoom : L+1<(σ.arrs "short.raw").length
  simpleRoom : L+1<(σ.arrs "short.simple").length

structure Buffers {n L : ℕ} (xs : List (Vertex n L)) (p : Vertex n L) (ys : List (Fin n)) (σ : Env) : Prop where
  raw : Prefix (vertices xs) "short.raw" σ
  rawLength : σ.vars "short.rawLength"=xs.length
  stack : Prefix (simple ys) "short.simple" σ
  stackLength : σ.vars "short.simpleLength"=ys.length
  vertex : σ.vars "short.vertex"=p.2.val
  level : σ.vars "short.level"=p.1.val

def names : List String := ["lp.n","lp.n2","short.layer","short.layerArcs","short.commodity","short.source"]
def bufferNames : List String := ["short.rawLength","short.simpleLength","short.vertex","short.level"]

theorem data_frame {B K : ℕ} {c : Com} {σ τ : Env} (rr : Run B c σ τ K)
    {n L : ℕ} {qs : Fin (1+(n*n)*(L*(n*n))) → ℚ≥0} {st : Edge n} (h : Data qs st σ)
    (hx : ∀ x∈names,x∉c.wvars) (ha : "flow.primal"∉c.warrs) : Data qs st τ := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (rr.frame_var _ (hx _ (by simp [names]))).trans h.order
  · exact (rr.frame_var _ (hx _ (by simp [names]))).trans h.square
  · exact (rr.frame_var _ (hx _ (by simp [names]))).trans h.layer
  · exact (rr.frame_var _ (hx _ (by simp [names]))).trans h.layerArcs
  · exact (rr.frame_var _ (hx _ (by simp [names]))).trans h.commodity
  · exact (rr.frame_var _ (hx _ (by simp [names]))).trans h.source
  · simpa only [Prefix,rr.frame_arr _ ha] using h.buffer
  · simpa only [RamFrames.run_array_length rr "short.raw"] using h.rawRoom
  · simpa only [RamFrames.run_array_length rr "short.simple"] using h.simpleRoom

/-- After an in-place residual update, preserve the source dimensions and
path buffer extents while replacing the typed primal-buffer view. -/
theorem replace_data {B K : ℕ} {c : Com} {σ τ : Env} (rr : Run B c σ τ K)
    {n L : ℕ} {q q' : Fin (1+(n*n)*(L*(n*n))) → ℚ≥0} {st : Edge n} (h : Data q st σ)
    (hx : ∀ x∈names,x∉c.wvars)
    (hp : Prefix (RamUnsignedBuffer.encode (List.ofFn q')) "flow.primal" τ) : Data q' st τ := by
  refine ⟨?_,?_,?_,?_,?_,?_,hp,?_,?_⟩
  · exact (rr.frame_var _ (hx _ (by simp [names]))).trans h.order
  · exact (rr.frame_var _ (hx _ (by simp [names]))).trans h.square
  · exact (rr.frame_var _ (hx _ (by simp [names]))).trans h.layer
  · exact (rr.frame_var _ (hx _ (by simp [names]))).trans h.layerArcs
  · exact (rr.frame_var _ (hx _ (by simp [names]))).trans h.commodity
  · exact (rr.frame_var _ (hx _ (by simp [names]))).trans h.source
  · simpa only [RamFrames.run_array_length rr "short.raw"] using h.rawRoom
  · simpa only [RamFrames.run_array_length rr "short.simple"] using h.simpleRoom

theorem set_var {n L : ℕ} {qs : Fin (1+(n*n)*(L*(n*n))) → ℚ≥0} {st : Edge n} {σ : Env}
    (h : Data qs st σ) (name : String) (value : ℕ) (hx : name∉names) : Data qs st (σ.setVar name value) := by
  have hne (x : String) (hm : x∈names) : x≠name := by intro he; exact hx (he ▸ hm)
  refine ⟨?_,?_,?_,?_,?_,?_,h.buffer,h.rawRoom,h.simpleRoom⟩
  · simpa only [vars_setVar,if_neg (hne "lp.n" (by simp [names]))] using h.order
  · simpa only [vars_setVar,if_neg (hne "lp.n2" (by simp [names]))] using h.square
  · simpa only [vars_setVar,if_neg (hne "short.layer" (by simp [names]))] using h.layer
  · simpa only [vars_setVar,if_neg (hne "short.layerArcs" (by simp [names]))] using h.layerArcs
  · simpa only [vars_setVar,if_neg (hne "short.commodity" (by simp [names]))] using h.commodity
  · simpa only [vars_setVar,if_neg (hne "short.source" (by simp [names]))] using h.source

theorem buffers_frame {B K : ℕ} {c : Com} {σ τ : Env} (rr : Run B c σ τ K)
    {n L : ℕ} {xs : List (Vertex n L)} {p : Vertex n L} {ys : List (Fin n)} (h : Buffers xs p ys σ)
    (hx : ∀ x∈bufferNames,x∉c.wvars) (ha : "short.raw"∉c.warrs) (hs : "short.simple"∉c.warrs) :
    Buffers xs p ys τ := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · simpa only [Prefix,rr.frame_arr _ ha] using h.raw
  · exact (rr.frame_var _ (hx _ (by simp [bufferNames]))).trans h.rawLength
  · simpa only [Prefix,rr.frame_arr _ hs] using h.stack
  · exact (rr.frame_var _ (hx _ (by simp [bufferNames]))).trans h.stackLength
  · exact (rr.frame_var _ (hx _ (by simp [bufferNames]))).trans h.vertex
  · exact (rr.frame_var _ (hx _ (by simp [bufferNames]))).trans h.level

/-- The loop invariant carries the exact raw path, simple stack, and
residual source buffer, all tied to the runtime counters and current vertex. -/
def Invariant {n L : ℕ} (qs : Fin (1+(n*n)*(L*(n*n))) → ℚ≥0) (st : Edge n) (σ : Env) : Prop :=
  Data qs st σ ∧ ∃ xs p ys,Walk qs st xs p ys ∧ Buffers xs p ys σ

theorem level_bound {n L : ℕ} {qs : Fin (1+(n*n)*(L*(n*n))) → ℚ≥0} {st : Edge n} {σ : Env}
    (h : Invariant qs st σ) : σ.vars "short.level"≤L := by
  obtain ⟨_,xs,p,ys,hw,hb⟩ := h
  rw [hb.level]
  omega

theorem limit {n L : ℕ} {qs : Fin (1+(n*n)*(L*(n*n))) → ℚ≥0} {st : Edge n} {σ : Env}
    (h : Invariant qs st σ) : σ.vars "short.layer"=L := h.1.layer

end Lax455465Proofs.RamPathState
