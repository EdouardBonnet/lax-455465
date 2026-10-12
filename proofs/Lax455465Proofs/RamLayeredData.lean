import Lax455465Proofs.RamLayeredCoefficient
import Lax455465Proofs.RamFlowData
import Lax455465Proofs.LayeredLpSize

namespace Lax455465Proofs.RamLayeredData
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState LayeredLpFlat
open Lax455465.RationalEncoding

structure Data {n : ℕ} (I : RationalInstance n) (L : ℕ) (σ : Env) : Prop where
  order : σ.vars "lp.n"=n
  square : σ.vars "lp.n2"=n*n
  layer : σ.vars "short.layer"=L
  layerArcs : σ.vars "short.layerArcs"=L*(n*n)
  layerVertices : σ.vars "short.layerVertices"=(L+1)*n
  balances : σ.vars "short.balances"=(n*n)*((L+1)*n)
  rowCount : σ.vars "lp.rows"=rows n L
  columnCount : σ.vars "lp.columns"=columns n L
  matrixLength : σ.vars "lp.matrixLength"=rows n L*columns n L
  capacities : Prefix (RamUnsignedBuffer.encode (RamFlowData.capacities I)) "flow.capacities" σ

def protectedVars : List String := ["lp.n","lp.n2","short.layer","short.layerArcs",
  "short.layerVertices","short.balances","lp.rows","lp.columns","lp.matrixLength"]

theorem frame {B K : ℕ} {c : Com} {σ τ : Env} (hr : Run B c σ τ K)
    {n : ℕ} (I : RationalInstance n) (L : ℕ) (h : Data I L σ)
    (ha : "flow.capacities"∉c.warrs) (hx : ∀ x∈protectedVars,x∉c.wvars) : Data I L τ := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (hr.frame_var _ (hx _ (by simp [protectedVars]))).trans h.order
  · exact (hr.frame_var _ (hx _ (by simp [protectedVars]))).trans h.square
  · exact (hr.frame_var _ (hx _ (by simp [protectedVars]))).trans h.layer
  · exact (hr.frame_var _ (hx _ (by simp [protectedVars]))).trans h.layerArcs
  · exact (hr.frame_var _ (hx _ (by simp [protectedVars]))).trans h.layerVertices
  · exact (hr.frame_var _ (hx _ (by simp [protectedVars]))).trans h.balances
  · exact (hr.frame_var _ (hx _ (by simp [protectedVars]))).trans h.rowCount
  · exact (hr.frame_var _ (hx _ (by simp [protectedVars]))).trans h.columnCount
  · exact (hr.frame_var _ (hx _ (by simp [protectedVars]))).trans h.matrixLength
  · simpa only [Prefix,hr.frame_arr "flow.capacities" ha] using h.capacities

theorem set_index {n : ℕ} (I : RationalInstance n) (L : ℕ) (σ : Env)
    (index : String) (k : ℕ) (h : Data I L σ) (hx : ∀ x∈protectedVars,x ≠ index) :
    Data I L (σ.setVar index k) := by
  have he (x : String) (hmem : x∈protectedVars) : (σ.setVar index k).vars x=σ.vars x := by
    simp only [vars_setVar,if_neg (hx x hmem)]
  exact ⟨(he _ (by simp [protectedVars])).trans h.order,
    (he _ (by simp [protectedVars])).trans h.square,
    (he _ (by simp [protectedVars])).trans h.layer,
    (he _ (by simp [protectedVars])).trans h.layerArcs,
    (he _ (by simp [protectedVars])).trans h.layerVertices,
    (he _ (by simp [protectedVars])).trans h.balances,
    (he _ (by simp [protectedVars])).trans h.rowCount,
    (he _ (by simp [protectedVars])).trans h.columnCount,
    (he _ (by simp [protectedVars])).trans h.matrixLength,h.capacities⟩

theorem context {n : ℕ} {I : RationalInstance n} {L : ℕ} {σ : Env} (h : Data I L σ)
    (i j : ℕ) (hi : σ.vars "lp.i"=i) (hj : σ.vars "lp.j"=j) : RamLayeredContext.Context n L i j σ :=
  ⟨h.order,h.square,h.layer,h.layerArcs,h.layerVertices,h.balances,hi,hj⟩

def shapeSize (n L : ℕ) : ℕ := n+n*n+L+L*(n*n)+(L+1)*n+(n*n)*((L+1)*n)+
  rows n L+columns n L+rows n L*columns n L+10

def dimensions : Com :=
  .seq (.assign "short.layerArcs" (.mul (.var "short.layer") (.var "lp.n2")))
  (.seq (.assign "short.layerVertices" (.mul (.add (.var "short.layer") (.lit 1)) (.var "lp.n")))
  (.seq (.assign "short.balances" (.mul (.var "lp.n2") (.var "short.layerVertices")))
  (.seq (.assign "lp.rows" (.add (.var "lp.n2") (.mul (.lit 2) (.var "short.balances"))))
  (.seq (.assign "lp.columns" (.add (.lit 1) (.mul (.var "lp.n2") (.var "short.layerArcs"))))
    (.assign "lp.matrixLength" (.mul (.var "lp.rows") (.var "lp.columns")))))))

theorem dimensions_spec (B n L : ℕ) (hB : shapeSize n L < B) :
    Spec B (fun σ => σ.vars "lp.n"=n ∧ σ.vars "lp.n2"=n*n ∧ σ.vars "short.layer"=L) dimensions
      (fun _ τ => τ.vars "short.layerArcs"=L*(n*n) ∧ τ.vars "short.layerVertices"=(L+1)*n ∧
        τ.vars "short.balances"=(n*n)*((L+1)*n) ∧ τ.vars "lp.rows"=rows n L ∧
        τ.vars "lp.columns"=columns n L ∧ τ.vars "lp.matrixLength"=rows n L*columns n L) 30 := by
  have hsmall : n < B ∧ n*n < B ∧ L+1 < B ∧ L*(n*n) < B ∧ (L+1)*n < B ∧
      (n*n)*((L+1)*n) < B ∧ 2*((n*n)*((L+1)*n)) < B ∧
      (n*n)*(L*(n*n)) < B ∧ rows n L < B ∧ columns n L < B ∧ rows n L*columns n L < B := by
    dsimp only [shapeSize,rows,columns] at hB ⊢
    omega
  rcases hsmall with ⟨hn,hn2,hL,hA,hV,hM,hM2,hC,hr,hc,hm⟩
  have h1 : 1 < B := by omega
  have h2 : 2 < B := by dsimp only [shapeSize] at hB; omega
  have hL' : L < B := by omega
  rintro σ ⟨hnσ,hn2σ,hLσ⟩
  run_vcg
  all_goals simp_all [rows,columns]

theorem from_graph (B : ℕ) {n : ℕ} (I : RationalInstance n) (L : ℕ) (hB : shapeSize n L < B) :
    Spec B (fun σ => RamFlowData.Data I σ ∧ σ.vars "short.layer"=L) dimensions
      (fun _ τ => Data I L τ) 30 := by
  rintro σ ⟨hgraph,hL⟩
  obtain ⟨τ,hr,hp⟩ := dimensions_spec B n L hB σ ⟨hgraph.1,hgraph.2.1,hL⟩
  refine ⟨τ,hr,?_,?_,?_,hp.1,hp.2.1,hp.2.2.1,hp.2.2.2.1,hp.2.2.2.2.1,hp.2.2.2.2.2,?_⟩
  · exact (hr.frame_var "lp.n" (by decide)).trans hgraph.1
  · exact (hr.frame_var "lp.n2" (by decide)).trans hgraph.2.1
  · exact (hr.frame_var "short.layer" (by decide)).trans hL
  · simpa only [Prefix,hr.frame_arr "flow.capacities" (by decide)] using hgraph.2.2.2.2.2.2.2

end Lax455465Proofs.RamLayeredData
