import Lax455465Proofs.RamLayeredSource
import Lax455465Proofs.RamUnsignedSum
import Lax455465Proofs.FlowLpIndices

namespace Lax455465Proofs.RamIncidentSum
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamVirtualState RamLayeredSource
open Lax455465.RationalEncoding
open scoped NNRat BigOperators

def row {n : ℕ} (I : RationalInstance n) (v : Fin n) : List ℚ≥0 := List.ofFn (I.capacity v)

def entry : Com := .seq
  (.assign "short.entry" (.add (.mul (.var "short.row") (.var "lp.n")) (.var "short.column")))
  (RamUnsignedBuffer.read "flow.capacities" "short.entry")

def Context {n : ℕ} (I : RationalInstance n) (v : Fin n) (σ : Env) : Prop :=
  Source I σ ∧ σ.vars "short.row"=v.val

theorem context_frame {B K : ℕ} {c : Com} {σ τ : Env} (hr : Run B c σ τ K)
    {n : ℕ} {I : RationalInstance n} {v : Fin n} (h : Context I v σ)
    (hn : "lp.n"∉c.wvars) (hn2 : "lp.n2"∉c.wvars)
    (ha : "flow.capacities"∉c.warrs) (hv : "short.row"∉c.wvars) : Context I v τ :=
  ⟨RamLayeredSource.frame hr h.1 hn hn2 ha,(hr.frame_var _ hv).trans h.2⟩

theorem capacities_at {n : ℕ} (I : RationalInstance n) (v w : Fin n) :
    (RamFlowData.capacities I)[(DirectedFlowLP.edgeIndex n (v,w)).val]'(by
      simp only [RamFlowData.capacities,List.length_ofFn]; exact (DirectedFlowLP.edgeIndex n (v,w)).isLt)=I.capacity v w := by
  simp only [RamFlowData.capacities,List.getElem_ofFn,Fin.eta,Equiv.symm_apply_apply]

theorem entry_spec (B M : ℕ) {n : ℕ} (I : RationalInstance n) (v w : Fin n)
    (hindex : 2*(n*n)+3 < B) (hMB : M < B)
    (hnum : (I.capacity v w).num ≤ M) (hden : (I.capacity v w).den ≤ M) :
    Spec B (fun σ => Context I v σ ∧ σ.vars "short.column"=w.val) entry
      (fun _ τ => Context I v τ ∧ FractionOutput (I.capacity v w : ℚ) τ) 20 := by
  let k := (DirectedFlowLP.edgeIndex n (v,w)).val
  have hk : k=v.val*n+w.val := FlowLpIndices.edge_value v w
  have hkn : k<n*n := (DirectedFlowLP.edgeIndex n (v,w)).isLt
  have hsmall : n<B ∧ v.val<B ∧ w.val<B ∧ v.val*n<B ∧ v.val*n+w.val<B := by
    have hn : n≤n*n := by nlinarith [v.isLt]
    omega
  rintro σ ⟨hcontext,hw⟩
  have hnσ := hcontext.1.order
  have hvσ := hcontext.2
  let ν := σ.setVar "short.entry" k
  have rindex : Run B (.assign "short.entry" (.add (.mul (.var "short.row") (.var "lp.n"))
      (.var "short.column"))) σ ν 6 := by
    convert Run.assign (σ := σ) (evalB_bin (op := .add)
      (evalB_bin (op := .mul) (by rw [evalB_var_iff]; exact ⟨hvσ.symm,hvσ ▸ hsmall.2.1⟩)
        (by rw [evalB_var_iff]; exact ⟨hnσ.symm,hnσ ▸ hsmall.1⟩) hsmall.2.2.2.1)
      (by rw [evalB_var_iff]; exact ⟨hw.symm,hw ▸ hsmall.2.2.1⟩) hsmall.2.2.2.2) using 1
    all_goals simp only [ν,Bop.apply,hk,Expr.size]
  have hq := capacities_at I v w
  obtain ⟨τ,rr,pr⟩ := RamUnsignedBuffer.read_spec B "flow.capacities" "short.entry"
    (RamFlowData.capacities I) k (by simpa [RamFlowData.capacities] using hkn) (by omega)
    (by omega) (by rw [hq]; exact hnum.trans_lt hMB) (by rw [hq]; exact hden.trans_lt hMB)
    (by decide) ν ⟨by simpa only [ν,Prefix,arrs_setVar] using hcontext.1.capacities,by simp [ν]⟩
  exact ⟨τ,rindex.seq rr,context_frame (rindex.seq rr) hcontext (by decide) (by decide) (by decide) (by decide),
    by simpa only [k,hq] using pr.1⟩

def command : Com := RamUnsignedSum.command "short.column" "lp.n" entry

theorem command_spec (B M : ℕ) {n : ℕ} (I : RationalInstance n) (v : Fin n)
    (hB : 2*M^2+3 < B) (hindex : 2*(n*n)+3 < B)
    (hnum : ∀ w,(I.capacity v w).num ≤ M) (hden : ∀ w,(I.capacity v w).den ≤ M)
    (hprefixNum : ∀ i,((row I v).take i).sum.num ≤ M)
    (hprefixDen : ∀ i,((row I v).take i).sum.den ≤ M) :
    Spec B (Context I v) command
      (fun _ τ => Context I v τ ∧ FractionOutput (((row I v).sum : ℚ≥0) : ℚ) τ)
      ((36*(M^2).size+140)*n+16) := by
  have hMB : M<B := by nlinarith only [hB]
  have hn : n<B := by nlinarith only [hindex]
  have hbody : ∀ i,∀ hi : i<(row I v).length,
      Spec B (fun σ => Context I v σ ∧ σ.vars "short.column"=i) entry
        (fun _ τ => Context I v τ ∧ FractionOutput ((row I v)[i] : ℚ) τ) 20 := by
    intro i hi
    have hin : i<n := by simpa [row] using hi
    simpa only [row,List.getElem_ofFn] using entry_spec B M I v ⟨i,hin⟩ hindex hMB (hnum _) (hden _)
  have hrun := RamUnsignedSum.command_spec B M 20 (Context I v) "short.column" "lp.n" (row I v) entry
    hB (by simpa [row] using hn)
    (by intro q hq; obtain ⟨w,rfl⟩ := List.mem_ofFn.mp hq; exact hnum w)
    (by intro q hq; obtain ⟨w,rfl⟩ := List.mem_ofFn.mp hq; exact hden w)
    hprefixNum hprefixDen
    (fun σ h => by simpa [row] using h.1.order)
    (by
      intro σ k name h hh
      rcases hh with rfl | rfl | rfl
      all_goals refine ⟨⟨?_,?_,?_⟩,?_⟩
      all_goals first
        | simpa only [vars_setVar,String.reduceEq,if_false] using h.1.order
        | simpa only [vars_setVar,String.reduceEq,if_false] using h.1.square
        | simpa only [Prefix,arrs_setVar] using h.1.capacities
        | simpa only [vars_setVar,String.reduceEq,if_false] using h.2)
    hbody (by decide) (by decide) (by decide)
    (fun rr h => context_frame rr h (by decide) (by decide) (by decide) (by decide))
    (fun rr h => context_frame rr h (by decide) (by decide) (by decide) (by decide))
  have hcost : (20+36*(M^2).size+120)*(row I v).length+16=(36*(M^2).size+140)*n+16 := by
    simp only [row,List.length_ofFn]
    ring
  simpa only [command,hcost] using hrun

end Lax455465Proofs.RamIncidentSum
