import Lax455465Proofs.RamLayeredIndices
import Lax455465Proofs.RamLayeredUnits

namespace Lax455465Proofs.RamLayeredContext
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning LayeredLpFlat

def Context (n L i j : ℕ) (σ : Env) : Prop :=
  σ.vars "lp.n"=n ∧ σ.vars "lp.n2"=n*n ∧ σ.vars "short.layer"=L ∧
  σ.vars "short.layerArcs"=L*(n*n) ∧ σ.vars "short.layerVertices"=(L+1)*n ∧
  σ.vars "short.balances"=(n*n)*((L+1)*n) ∧ σ.vars "lp.i"=i ∧ σ.vars "lp.j"=j

def contextNames : List String := ["lp.n","lp.n2","short.layer","short.layerArcs",
  "short.layerVertices","short.balances","lp.i","lp.j"]

theorem frame {B K : ℕ} {c : Com} {σ τ : Env} (hr : Run B c σ τ K)
    (n L i j : ℕ) (h : Context n L i j σ) (hx : ∀ x∈contextNames,x∉c.wvars) : Context n L i j τ := by
  have hn := hr.frame_var "lp.n" (hx _ (by simp [contextNames]))
  have hn2 := hr.frame_var "lp.n2" (hx _ (by simp [contextNames]))
  have hL := hr.frame_var "short.layer" (hx _ (by simp [contextNames]))
  have hA := hr.frame_var "short.layerArcs" (hx _ (by simp [contextNames]))
  have hV := hr.frame_var "short.layerVertices" (hx _ (by simp [contextNames]))
  have hM := hr.frame_var "short.balances" (hx _ (by simp [contextNames]))
  have hi := hr.frame_var "lp.i" (hx _ (by simp [contextNames]))
  have hj := hr.frame_var "lp.j" (hx _ (by simp [contextNames]))
  simpa only [Context,hn,hn2,hL,hA,hV,hM,hi,hj] using h

def capDecode : Com := .seq (.assign "short.capSource" (.div (.var "lp.i") (.var "lp.n")))
  (.assign "short.capTarget" (.sub (.var "lp.i") (.mul (.var "short.capSource") (.var "lp.n"))))

theorem capDecode_spec (B n i : ℕ) (hn : n < B) (hi : i < B) :
    Spec B (fun σ => σ.vars "lp.n"=n ∧ σ.vars "lp.i"=i) capDecode
      (fun _ τ => τ.vars "short.capSource"=i/n ∧ τ.vars "short.capTarget"=i%n) 10 := by
  have hd : i/n < B := (Nat.div_le_self _ _).trans_lt hi
  have hp : i/n*n < B := (Nat.div_mul_le_self _ _).trans_lt hi
  have hm : i%n < B := (Nat.mod_le _ _).trans_lt hi
  rintro σ ⟨hσn,hσi⟩
  run_vcg
  all_goals simp_all [Nat.mod_def,Nat.mul_comm]

def prepare : Com := .seq RamLayeredIndices.column (.seq RamLayeredIndices.row capDecode)

def Prepared (n L i j : ℕ) (σ : Env) : Prop := Context n L i j σ ∧
  σ.vars "short.arcCommodity"=arcCommodity n L j ∧ σ.vars "short.arcLayer"=arcLayer n L j ∧
  σ.vars "short.arcSource"=arcSource n L j ∧ σ.vars "short.arcTarget"=arcTarget n L j ∧
  σ.vars "short.rowSign"=rowSign n L i ∧ σ.vars "short.rowCommodity"=rowCommodity n L i ∧
  σ.vars "short.rowLayer"=rowLayer n L i ∧ σ.vars "short.rowVertex"=rowVertex n L i ∧
  σ.vars "short.s"=rowCommodity n L i/n ∧ σ.vars "short.t"=rowCommodity n L i%n ∧
  σ.vars "short.capSource"=i/n ∧ σ.vars "short.capTarget"=i%n

theorem prepare_spec (B n L i j : ℕ) (h1 : 1 < B) (hn : n < B) (hn2 : n*n < B)
    (hA : L*(n*n) < B) (hV : (L+1)*n < B) (hM : (n*n)*((L+1)*n) < B)
    (hi : i < B) (hj : j < B) :
    Spec B (Context n L i j) prepare (fun _ τ => Prepared n L i j τ) 88 := by
  intro σ hctx
  rcases hctx with ⟨hnσ,hn2σ,hLσ,hAσ,hVσ,hMσ,hiσ,hjσ⟩
  have hctx : Context n L i j σ := ⟨hnσ,hn2σ,hLσ,hAσ,hVσ,hMσ,hiσ,hjσ⟩
  obtain ⟨ν,hcol,hcols⟩ := RamLayeredIndices.column_spec B n (n*n) (L*(n*n)) j h1 hn hn2 hA hj σ
    ⟨hnσ,hn2σ,hAσ,hjσ⟩
  have hctxν := frame hcol n L i j hctx (by decide)
  obtain ⟨μ,hrow,hrows⟩ := RamLayeredIndices.row_spec B n (n*n) ((L+1)*n) ((n*n)*((L+1)*n)) i
    hn hn2 hV hM hi ν ⟨hctxν.1,hctxν.2.1,hctxν.2.2.2.2.1,hctxν.2.2.2.2.2.1,hctxν.2.2.2.2.2.2.1⟩
  have hctxμ := frame hrow n L i j hctxν (by decide)
  obtain ⟨τ,hcap,hcaps⟩ := capDecode_spec B n i hn hi μ ⟨hctxμ.1,hctxμ.2.2.2.2.2.2.1⟩
  have hctxτ := frame hcap n L i j hctxμ (by decide)
  have htail := hrow.seq hcap
  rcases hcols with ⟨hac,_,hk,_,hu,hv⟩
  rcases hrows with ⟨hflag,_,hrc,_,hrk,hru,hs,ht⟩
  refine ⟨τ,hcol.seq htail,hctxτ,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,hcaps⟩
  · exact (htail.frame_var "short.arcCommodity" (by decide)).trans hac
  · exact (htail.frame_var "short.arcLayer" (by decide)).trans hk
  · exact (htail.frame_var "short.arcSource" (by decide)).trans hu
  · exact (htail.frame_var "short.arcTarget" (by decide)).trans hv
  · exact (hcap.frame_var "short.rowSign" (by decide)).trans hflag
  · exact (hcap.frame_var "short.rowCommodity" (by decide)).trans hrc
  · exact (hcap.frame_var "short.rowLayer" (by decide)).trans hrk
  · exact (hcap.frame_var "short.rowVertex" (by decide)).trans hru
  · exact (hcap.frame_var "short.s" (by decide)).trans hs
  · exact (hcap.frame_var "short.t" (by decide)).trans ht

end Lax455465Proofs.RamLayeredContext
