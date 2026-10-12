import Lax455465Proofs.RamPathInit
import Lax455465Proofs.RamPathExtend

namespace Lax455465Proofs.RamPositivePath
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState
open LayeredFlowLP LayeredGraphFlow LayeredWalkState RamPathState
open scoped NNRat

def scan : Com := .seq (.assign "short.level" (.lit 0))
  (.while (.lt (.var "short.level") (.var "short.layer")) RamPathExtend.command)

def command : Com := .seq RamPathInit.command scan

/-- The fixed native traversal constructs a complete positive layered
source-to-target path and its simple physical projection. -/
theorem command_spec (B : ℕ) {n L : ℕ} (qs : Fin (1+(n*n)*(L*(n*n))) → ℚ≥0)
    (st : Edge n) (a : ℚ) (ha : 0<a) (hL : 1≤L)
    (hb : AcyclicFlowPath.Balance (graph (arc qs) st) (0,st.1) (Fin.last L,st.2) a)
    (hsize : n+n*n+L*(n*n)+2*(1+(n*n)*(L*(n*n)))+2*L+20<B)
    (hnum : ∀ j,(qs j).num<B) (hden : ∀ j,(qs j).den<B) :
    Spec B (Data qs st) command
      (fun _ τ => Data qs st τ ∧ ∃ xs ys,
        Walk qs st xs (Fin.last L,st.2) ys ∧ Buffers xs (Fin.last L,st.2) ys τ)
      ((100*n+100*L+204)*L+70) := by
  have hnB : n<B := by omega
  have hLB : L<B := by omega
  have h1 : 1<B := by omega
  have hscan := Spec.forRangeZero "short.level" "short.layer" (Invariant qs st) L
    (100*n+100*L+200) hLB (fun _ h => level_bound h) (fun _ h => limit h)
    (RamPathExtend.command_spec B qs st a ha hb hsize hnum hden)
  intro σ hd
  obtain ⟨ν,ri,pi⟩ := RamPathInit.command_spec B qs st hnB h1 σ hd
  have hinit : Invariant qs st (ν.setVar "short.level" 0) := by
    have rr : Run B (.assign "short.level" (.lit 0)) ν (ν.setVar "short.level" 0) 2 :=
      Run.assign (evalB_lit (by omega))
    refine ⟨data_frame rr pi.1 (by decide) (by decide),[(0,st.1)],(0,st.1),[st.1],initial qs st,?_,?_,?_,?_,?_,?_⟩
    · exact pi.2.raw
    · simpa only [vars_setVar,String.reduceEq,if_false] using pi.2.rawLength
    · exact pi.2.stack
    · simpa only [vars_setVar,String.reduceEq,if_false] using pi.2.stackLength
    · simpa only [vars_setVar,String.reduceEq,if_false] using pi.2.vertex
    · simp
  obtain ⟨τ,rs,ps⟩ := hscan ν hinit
  obtain ⟨hdτ,xs,p,ys,hw,hbuf⟩ := ps.1
  have hp : p.1.val=L := hbuf.level.symm.trans ps.2
  have ht : p.2=st.2 := target qs st hw hL hp a ha.le hb
  have he : p=(Fin.last L,st.2) := Prod.ext (Fin.ext hp) ht
  subst p
  exact ⟨τ,(ri.seq rs).mono (by ring_nf; omega),hdτ,xs,ys,hw,hbuf⟩

end Lax455465Proofs.RamPositivePath
