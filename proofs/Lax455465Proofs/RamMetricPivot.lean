import Lax455465Proofs.RamMetricIndices
import Lax455465Proofs.RamMinPlus
import Lax455465Proofs.RamUnsignedVector
import Lax455465Proofs.MetricMatrix

namespace Lax455465Proofs.RamMetricPivot

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamRational DirectedFlowLP MetricMatrix
open scoped NNRat

def Context {n : ℕ} (p : Fin n) (d : Matrix n) (σ : Env) : Prop :=
  σ.vars "metric.n" = n ∧ σ.vars "metric.n2" = n*n ∧ σ.vars "metric.p" = p.val ∧
    Prefix (RamUnsignedBuffer.encode (values d)) "metric.old" σ

theorem frame {B K : ℕ} {cmd : Com} {σ τ : Env} (hr : Run B cmd σ τ K)
    {n : ℕ} {p : Fin n} {d : Matrix n} (h : Context p d σ)
    (ha : "metric.old" ∉ cmd.warrs)
    (hx : ∀ x ∈ ["metric.n","metric.n2","metric.p"], x ∉ cmd.wvars) : Context p d τ := by
  simpa only [Context,Prefix,hr.frame_arr "metric.old" ha,
    hr.frame_var "metric.n" (hx _ (by simp)),hr.frame_var "metric.n2" (hx _ (by simp)),
    hr.frame_var "metric.p" (hx _ (by simp))] using h

def entry : Com := .seq RamMetricIndices.command RamMinPlus.command

theorem entry_spec (B H : ℕ) {n : ℕ} (d : Matrix n) (p : Fin n) (e : Fin (n*n))
    (hB : 2*(2*H)^2+3 < B) (hn : n < B) (hn2 : n*n < B) (hindex : 2*(n*n)+1 < B)
    (hnum : ∀ u v, (d u v).num ≤ H) (hden : ∀ u v, (d u v).den ≤ H)
    (hsnum : ∀ u v, (d u p+d p v).num ≤ 2*H)
    (hsden : ∀ u v, (d u p+d p v).den ≤ 2*H) :
    Spec B (fun σ => Context p d σ ∧ σ.vars "metric.entry" = e.val) entry
      (fun _ τ => Context p d τ ∧ FractionOutput ((values (MetricMatrix.step d p))[e.val] : ℚ) τ)
      (36*(H*H).size+242) := by
  let u := ((edgeIndex n).symm e).1
  let v := ((edgeIndex n).symm e).2
  let a := (edgeIndex n (u,v)).val
  let b := (edgeIndex n (u,p)).val
  let c := (edgeIndex n (p,v)).val
  have he : edgeIndex n (u,v) = e := (edgeIndex n).apply_symm_apply e
  have ha : a < (values d).length := by simpa only [a,length_values] using (edgeIndex n (u,v)).isLt
  have hb : b < (values d).length := by simpa only [b,length_values] using (edgeIndex n (u,p)).isLt
  have hc : c < (values d).length := by simpa only [c,length_values] using (edgeIndex n (p,v)).isLt
  have hva : (values d)[a] = d u v := value_at d u v
  have hvb : (values d)[b] = d u p := value_at d u p
  have hvc : (values d)[c] = d p v := value_at d p v
  rintro σ ⟨hctx,hentry⟩
  obtain ⟨ν,rindex,pindex⟩ := RamMetricIndices.command_spec B u v p hn hn2 σ
    ⟨hctx.1,hctx.2.2.1,by simpa only [he] using hentry⟩
  have hctxν := frame rindex hctx (by decide) (by decide)
  obtain ⟨τ,rmin,pmin⟩ := RamMinPlus.command_spec B H (values d) a b c ha hb hc hB
    (by have := (edgeIndex n (u,v)).isLt; dsimp only [a]; omega)
    (by have := (edgeIndex n (u,p)).isLt; dsimp only [b]; omega)
    (by have := (edgeIndex n (p,v)).isLt; dsimp only [c]; omega)
    (by simpa only [hva] using hnum u v) (by simpa only [hva] using hden u v)
    (by simpa only [hvb] using hnum u p) (by simpa only [hvb] using hden u p)
    (by simpa only [hvc] using hnum p v) (by simpa only [hvc] using hden p v)
    (by simpa only [hvb,hvc] using hsnum u v) (by simpa only [hvb,hvc] using hsden u v) ν
      ⟨hctxν.2.2.2,pindex⟩
  have hcost : 36*((values d)[b].den*(values d)[c].den).size+218 ≤ 36*(H*H).size+218 := by
    have hdprod : (values d)[b].den*(values d)[c].den ≤ H*H := by
      rw [hvb,hvc]; exact Nat.mul_le_mul (hden u p) (hden p v)
    have := Nat.size_le_size hdprod
    omega
  refine ⟨τ,(rindex.seq rmin).mono (by omega),frame rmin hctxν (by decide) (by decide),?_⟩
  have hout : (values (MetricMatrix.step d p))[e.val] = MetricMatrix.step d p u v := by
    rw [←he]
    exact value_at _ _ _
  simpa only [hout,MetricMatrix.step,NNRat.coe_min,hva,hvb,hvc] using pmin

def build : Com := RamUnsignedVector.command "metric.entry" "metric.n2" "metric.new" "metric.position" entry

def command : Com := .seq (.assign "metric.position" (.lit 0)) build

/-- One runtime loop emits every entry of the precise immutable matrix
pivot into a second buffer. It retains the old matrix throughout the pivot. -/
theorem command_spec (B H : ℕ) {n : ℕ} (d : Matrix n) (p : Fin n)
    (hB : 2*(2*H)^2+3 < B) (hn : n < B) (hn2 : n*n < B) (hindex : 2*(n*n)+2 < B)
    (hnum : ∀ u v, (d u v).num ≤ H) (hden : ∀ u v, (d u v).den ≤ H)
    (hsnum : ∀ u v, (d u p+d p v).num ≤ 2*H)
    (hsden : ∀ u v, (d u p+d p v).den ≤ 2*H)
    (houtnum : ∀ u v, (MetricMatrix.step d p u v).num ≤ H)
    (houtden : ∀ u v, (MetricMatrix.step d p u v).den ≤ H) :
    Spec B (fun σ => Context p d σ ∧ 2*(n*n) < (σ.arrs "metric.new").length) command
      (fun _ τ => Context p d τ ∧ Prefix (RamUnsignedBuffer.encode (values (MetricMatrix.step d p))) "metric.new" τ ∧
        τ.vars "metric.position" = 2*(n*n)) ((36*(H*H).size+264)*(n*n)+8) := by
  have hH : H < B := by nlinarith
  let qs := values (MetricMatrix.step d p)
  have hlength : qs.length = n*n := length_values _
  have hvals : ∀ i, ∀ hi : i < qs.length,
      qs[i].num < B ∧ qs[i].den < B := by
    intro i hi
    have he : i < n*n := by rwa [hlength] at hi
    let uv := (edgeIndex n).symm (⟨i,he⟩ : Fin (n*n))
    have heq : qs[i] = MetricMatrix.step d p uv.1 uv.2 := by
      simp only [qs,values,List.getElem_ofFn,uv]
    rw [heq]
    exact ⟨(houtnum _ _).trans_lt hH,(houtden _ _).trans_lt hH⟩
  have hloop := RamUnsignedVector.command_spec B (36*(H*H).size+242) (Context p d)
    "metric.entry" "metric.n2" "metric.new" "metric.position" qs [] entry (by nlinarith)
    (by simp only [List.length_nil,hlength]; omega)
    (fun i hi => (hvals i hi).1) (fun i hi => (hvals i hi).2)
    (fun σ h => by simpa only [hlength] using h.2.1)
    (fun σ k h => by simpa only [Context,Prefix,vars_setVar,arrs_setVar,String.reduceEq,if_false] using h)
    (fun i hi => by
      have he : i < n*n := by rwa [hlength] at hi
      simpa only [qs] using entry_spec B H d p ⟨i,he⟩ hB hn hn2 (by omega) hnum hden hsnum hsden)
    (by decide) (by decide) (by decide) (by decide)
    (fun hr h => frame hr h (by decide) (by decide)) (by decide) (by decide)
  rintro σ ⟨hctx,hroom⟩
  let ν := σ.setVar "metric.position" 0
  have rzero : Run B (.assign "metric.position" (.lit 0)) σ ν 2 := Run.assign (evalB_lit (by nlinarith))
  have hctxν := frame rzero hctx (by decide) (by decide)
  obtain ⟨τ,hr,hpost⟩ := hloop ν ⟨hctxν,by intro i hi; simp at hi,by simp [ν],
    by simpa only [ν,arrs_setVar,hlength,List.length_nil,Nat.zero_add] using hroom⟩
  exact ⟨τ,(rzero.seq hr).mono (by simp only [hlength,Nat.add_assoc,Nat.reduceAdd]; omega),hpost.1,
    by simpa only [List.nil_append,qs] using hpost.2.1,
    by simpa only [List.length_nil,Nat.zero_add,hlength] using hpost.2.2⟩

end Lax455465Proofs.RamMetricPivot
