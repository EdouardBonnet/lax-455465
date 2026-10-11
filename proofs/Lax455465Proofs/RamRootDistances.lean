import Lax455465Proofs.RamUnsignedVector
import Lax455465Proofs.MetricMatrix

namespace Lax455465Proofs.RamRootDistances

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamRational MetricMatrix DirectedFlowLP
open scoped NNRat

def vector {n : ℕ} (outward : Bool) (root : Fin n) (d : Matrix n) : List ℚ≥0 :=
  List.ofFn fun v => if outward then d root v else d v root

@[simp] theorem length_vector {n : ℕ} (outward : Bool) (root : Fin n) (d : Matrix n) :
    (vector outward root d).length = n := List.length_ofFn

def array (outward : Bool) : String := if outward then "region.out" else "region.in"

def Context {n : ℕ} (root : Fin n) (d : Matrix n) (σ : Env) : Prop :=
  σ.vars "metric.n" = n ∧ σ.vars "region.root" = root.val ∧
    Prefix (RamUnsignedBuffer.encode (values d)) "metric.old" σ

theorem frame {B K : ℕ} {cmd : Com} {σ τ : Env} (hr : Run B cmd σ τ K)
    {n : ℕ} {root : Fin n} {d : Matrix n} (h : Context root d σ)
    (ha : "metric.old" ∉ cmd.warrs) (hn : "metric.n" ∉ cmd.wvars)
    (hroot : "region.root" ∉ cmd.wvars) : Context root d τ := by
  simpa only [Context,Prefix,hr.frame_arr "metric.old" ha,
    hr.frame_var "metric.n" hn,hr.frame_var "region.root" hroot] using h

def entry (outward : Bool) : Com := .seq
  (.assign "region.address" (if outward then .add (.mul (.var "region.root") (.var "metric.n")) (.var "region.i")
    else .add (.mul (.var "region.i") (.var "metric.n")) (.var "region.root")))
  (RamUnsignedBuffer.read "metric.old" "region.address")

theorem entry_spec (B H : ℕ) {n : ℕ} (outward : Bool) (root : Fin n) (d : Matrix n) (v : Fin n)
    (hH : H < B) (hn : n < B) (hn2 : n*n < B) (hindex : 2*(n*n)+2 < B)
    (hnum : ∀ u v, (d u v).num ≤ H) (hden : ∀ u v, (d u v).den ≤ H) :
    Spec B (fun σ => Context root d σ ∧ σ.vars "region.i" = v.val) (entry outward)
      (fun _ τ => Context root d τ ∧ FractionOutput ((vector outward root d)[v.val] : ℚ) τ) 20 := by
  let u := if outward then root else v
  let t := if outward then v else root
  let address := (edgeIndex n (u,t)).val
  have ha : address < n*n := (edgeIndex n (u,t)).isLt
  have hval : (values d)[address] = d u t := value_at d u t
  have hvector : (vector outward root d)[v.val] = d u t := by
    simp only [vector,List.getElem_ofFn,u,t]
    cases outward <;> rfl
  rintro σ ⟨hctx,hi⟩
  let ν := σ.setVar "region.address" address
  have haddr : Run B (.assign "region.address" (if outward then .add (.mul (.var "region.root") (.var "metric.n")) (.var "region.i")
      else .add (.mul (.var "region.i") (.var "metric.n")) (.var "region.root"))) σ ν 6 := by
    have hroot : root.val < B := root.isLt.trans hn
    have hv : v.val < B := v.isLt.trans hn
    have hprodR : root.val*n < B := (by nlinarith [root.isLt] : root.val*n < n*n).trans hn2
    have hprodV : v.val*n < B := (by nlinarith [v.isLt] : v.val*n < n*n).trans hn2
    cases outward with
    | false =>
      have heq : address = v.val*n+root.val := by simp [address,u,t,FlowLpIndices.edge_value]
      have hm := evalB_bin (op := .mul) (by rw [evalB_var_iff]; exact ⟨hi.symm,hi ▸ hv⟩)
        (by rw [evalB_var_iff]; exact ⟨hctx.1.symm,hctx.1 ▸ hn⟩) hprodV
      simpa only [Bool.false_eq_true,if_false,if_pos rfl,ν,heq,Expr.size,Bop.apply,Nat.reduceAdd,if_true] using (Run.assign (evalB_bin (op := .add) hm
        (by rw [evalB_var_iff]; exact ⟨hctx.2.1.symm,hctx.2.1 ▸ hroot⟩) (by change v.val*n+root.val < B; rw [←heq]; exact ha.trans hn2)) : Run B _ _ _ 6)
    | true =>
      have heq : address = root.val*n+v.val := by simp [address,u,t,FlowLpIndices.edge_value]
      have hm := evalB_bin (op := .mul) (by rw [evalB_var_iff]; exact ⟨hctx.2.1.symm,hctx.2.1 ▸ hroot⟩)
        (by rw [evalB_var_iff]; exact ⟨hctx.1.symm,hctx.1 ▸ hn⟩) hprodR
      simpa only [Bool.false_eq_true,if_false,if_pos rfl,ν,heq,Expr.size,Bop.apply,Nat.reduceAdd,if_true] using (Run.assign (evalB_bin (op := .add) hm
        (by rw [evalB_var_iff]; exact ⟨hi.symm,hi ▸ hv⟩) (by change root.val*n+v.val < B; rw [←heq]; exact ha.trans hn2)) : Run B _ _ _ 6)
  have hctxν := frame haddr hctx (by simp [Com.warrs]) (by simp [Com.wvars]) (by simp [Com.wvars])
  obtain ⟨τ,rr,pr⟩ := RamUnsignedBuffer.read_spec B "metric.old" "region.address" (values d) address
    (by simpa only [length_values] using ha) (by omega) (by omega)
    (by rw [hval]; exact (hnum u t).trans_lt hH) (by rw [hval]; exact (hden u t).trans_lt hH)
    (by decide) ν ⟨hctxν.2.2,by simp [ν]⟩
  refine ⟨τ,haddr.seq rr,frame rr hctxν (by decide) (by decide) (by decide),?_⟩
  simpa only [hval,hvector] using pr.1

def command (outward : Bool) : Com := .seq (.assign "region.pos" (.lit 0))
  (RamUnsignedVector.command "region.i" "metric.n" (array outward) "region.pos" (entry outward))

/-- Extract the exact outward or inward distance vector for a runtime root.
The distance matrix remains intact for all later region selections. -/
theorem command_spec (B H : ℕ) {n : ℕ} (outward : Bool) (root : Fin n) (d : Matrix n)
    (hH : H < B) (hn : n < B) (hn2 : n*n < B) (hindex : 2*(n*n)+2 < B)
    (hnum : ∀ u v, (d u v).num ≤ H) (hden : ∀ u v, (d u v).den ≤ H) :
    Spec B (fun σ => Context root d σ ∧ 2*n < (σ.arrs (array outward)).length) (command outward)
      (fun _ τ => Context root d τ ∧ Prefix (RamUnsignedBuffer.encode (vector outward root d)) (array outward) τ)
      (42*n+8) := by
  let qs := vector outward root d
  have hlen : qs.length = n := List.length_ofFn
  have hwords : ∀ i, ∀ hi : i < qs.length, qs[i].num < B ∧ qs[i].den < B := by
    intro i hi
    have hv : i < n := by rwa [hlen] at hi
    have heq : qs[i] = if outward then d root ⟨i,hv⟩ else d ⟨i,hv⟩ root := by
      dsimp only [qs,vector]
      erw [List.getElem_ofFn]
    rw [heq]
    cases outward <;> exact ⟨(hnum _ _).trans_lt hH,(hden _ _).trans_lt hH⟩
  have hloop := RamUnsignedVector.command_spec B 20 (Context root d)
    "region.i" "metric.n" (array outward) "region.pos" qs [] (entry outward) (by omega)
    (by have hnpositive := root.isLt; simp only [List.length_nil,hlen]; nlinarith)
    (fun i hi => (hwords i hi).1) (fun i hi => (hwords i hi).2)
    (fun σ h => by simpa only [hlen] using h.1)
    (fun σ k h => by simpa only [Context,Prefix,vars_setVar,arrs_setVar,String.reduceEq,if_false] using h)
    (fun i hi => by
      have hv : i < n := by rwa [hlen] at hi
      exact entry_spec B H outward root d ⟨i,hv⟩ hH hn hn2 hindex hnum hden)
    (by cases outward <;> decide) (by cases outward <;> decide) (by cases outward <;> decide)
    (by cases outward <;> decide)
    (fun rr h => frame rr h (by cases outward <;> decide) (by cases outward <;> decide) (by cases outward <;> decide))
    (by decide) (by decide)
  rintro σ ⟨hctx,hroom⟩
  let ν := σ.setVar "region.pos" 0
  have rzero : Run B (.assign "region.pos" (.lit 0)) σ ν 2 := Run.assign (evalB_lit (by omega))
  have hctxν := frame rzero hctx (by decide) (by decide) (by decide)
  obtain ⟨τ,rr,pr⟩ := hloop ν ⟨hctxν,by intro i hi; simp at hi,by simp [ν],
    by simpa only [ν,arrs_setVar,hlen,List.length_nil,Nat.zero_add] using hroom⟩
  exact ⟨τ,(rzero.seq rr).mono (by simp only [hlen]; omega),pr.1,by simpa only [List.nil_append,qs] using pr.2.1⟩

end Lax455465Proofs.RamRootDistances
