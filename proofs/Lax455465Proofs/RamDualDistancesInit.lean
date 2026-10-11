import Lax455465Proofs.RamOptimalDecode
import Lax455465Proofs.RamUnsignedVector
import Lax455465Proofs.RamFractionPrimitives
import Lax455465Proofs.MetricMatrix

namespace Lax455465Proofs.RamDualDistancesInit

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamRational DirectedFlowLP MetricMatrix
open scoped NNRat

def matrix {n : ℕ} (y : Fin (RamFlowData.rows n) → ℚ) (hy : ∀ i, 0 ≤ y i) : Matrix n :=
  fun u v => ⟨RationalDistances.zeroDiagonal (DirectedFlowDual.length y) u v,by
    apply RationalDistances.nonnegative_zeroDiagonal
    intro u v
    exact hy _⟩

theorem rational_matrix {n : ℕ} (y : Fin (RamFlowData.rows n) → ℚ) (hy : ∀ i, 0 ≤ y i) :
    rational (matrix y hy) = RationalDistances.zeroDiagonal (DirectedFlowDual.length y) := rfl

def indices : Com := .seq (.assign "metric.u" (.div (.var "metric.entry") (.var "metric.n")))
  (.assign "metric.v" (.sub (.var "metric.entry") (.mul (.var "metric.u") (.var "metric.n"))))

def coefficient : Com := .seq indices
  (.ite (.eq (.var "metric.u") (.var "metric.v")) RamFractionPrimitives.zero
    (RamUnsignedBuffer.read "flow.dual" "metric.entry"))

def Context {n : ℕ} (y : Fin (RamFlowData.rows n) → ℚ) (hy : ∀ i, 0 ≤ y i) (σ : Env) : Prop :=
  σ.vars "metric.n" = n ∧ σ.vars "metric.n2" = n*n ∧
    Prefix (RamUnsignedBuffer.encode (RamOptimalDecode.vector y hy)) "flow.dual" σ

theorem frame {B K : ℕ} {cmd : Com} {σ τ : Env} (hr : Run B cmd σ τ K)
    {n : ℕ} {y : Fin (RamFlowData.rows n) → ℚ} {hy : ∀ i, 0 ≤ y i} (h : Context y hy σ)
    (ha : "flow.dual" ∉ cmd.warrs)
    (hx : ∀ x ∈ ["metric.n","metric.n2"], x ∉ cmd.wvars) : Context y hy τ := by
  simpa only [Context,Prefix,hr.frame_arr "flow.dual" ha,
    hr.frame_var "metric.n" (hx _ (by simp)),hr.frame_var "metric.n2" (hx _ (by simp))] using h

theorem indices_spec (B : ℕ) {n : ℕ} (u v : Fin n) (hn : n < B) (hn2 : n*n < B) :
    Spec B (fun σ => σ.vars "metric.n" = n ∧ σ.vars "metric.entry" = (edgeIndex n (u,v)).val) indices
      (fun _ τ => τ.vars "metric.u" = u.val ∧ τ.vars "metric.v" = v.val) 10 := by
  have he : (edgeIndex n (u,v)).val < B := (edgeIndex n (u,v)).isLt.trans hn2
  have hu : u.val < B := u.isLt.trans hn
  have hv : v.val < B := v.isLt.trans hn
  have hmul : u.val*n < B := by rw [FlowLpIndices.edge_value] at he; omega
  have hdiv := FlowLpIndices.edge_div u v
  have hmod := FlowLpIndices.edge_mod u v
  rw [Nat.mod_def] at hmod
  rintro σ ⟨hnσ,heσ⟩
  run_vcg
  all_goals simp_all [FlowLpIndices.edge_value]

/-- Initialize one distance from the actual decoded capacity multiplier,
setting its diagonal to zero before the first min-plus pivot. -/
theorem coefficient_spec (B M : ℕ) {n : ℕ} (y : Fin (RamFlowData.rows n) → ℚ)
    (hy : ∀ i, 0 ≤ y i) (u v : Fin n) (h2 : 2 < B) (hM : M < B)
    (hn : n < B) (hn2 : n*n < B) (hindex : 2*(n*n)+1 < B)
    (hnum : ∀ i, (y i).num.natAbs ≤ M) (hden : ∀ i, (y i).den ≤ M) :
    Spec B (fun σ => Context y hy σ ∧ σ.vars "metric.entry" = (edgeIndex n (u,v)).val) coefficient
      (fun _ τ => Context y hy τ ∧ FractionOutput ((matrix y hy u v : ℚ≥0) : ℚ) τ) 28 := by
  rintro σ ⟨hctx,hentry⟩
  obtain ⟨ν,rindex,pindex⟩ := indices_spec B u v hn hn2 σ ⟨hctx.1,hentry⟩
  have hctxν := frame rindex hctx (by decide) (by decide)
  have hcond : (Cond.eq (.var "metric.u") (.var "metric.v")).evalB B ν = some (decide (u.val=v.val)) := by
    rw [evalB_condEq (by rw [evalB_var_iff]; exact ⟨pindex.1.symm,pindex.1 ▸ u.isLt.trans hn⟩)
      (by rw [evalB_var_iff]; exact ⟨pindex.2.symm,pindex.2 ▸ v.isLt.trans hn⟩)]
    congr 1
  by_cases huv : u = v
  · have hv : u.val = v.val := congrArg Fin.val huv
    obtain ⟨τ,rzero,pzero⟩ := RamFractionPrimitives.zero_spec B (by omega) ν True.intro
    have rbranch := Run.ite_true (d := RamUnsignedBuffer.read "flow.dual" "metric.entry") (by simpa only [hv,decide_true] using hcond) rzero
    refine ⟨τ,(rindex.seq rbranch).mono (by dsimp [Cond.size,Expr.size]; omega),frame rzero hctxν (by decide) (by decide),?_⟩
    simpa only [matrix,RationalDistances.zeroDiagonal,if_pos huv,NNRat.coe_mk] using pzero
  · let r : Fin (RamFlowData.rows n) := rowIndex n (.inl (u,v))
    have hrow : r.val = (edgeIndex n (u,v)).val := by
      simp only [r,FlowLpIndices.capacity_row,FlowLpIndices.edge_value]
    let qs := RamOptimalDecode.vector y hy
    have hqslen : qs.length = RamFlowData.rows n := RamOptimalDecode.length_vector y hy
    have hr : r.val < qs.length := by rw [hqslen]; exact r.isLt
    have hqr : qs[r.val] = (⟨y r,hy r⟩ : ℚ≥0) := by
      dsimp only [qs,RamOptimalDecode.vector]
      erw [List.getElem_ofFn]
    have hnq : qs[r.val].num < B := by
      rw [hqr]
      change (y r).num.natAbs < B
      exact (hnum r).trans_lt hM
    have hdq : qs[r.val].den < B := by
      rw [hqr]
      change (y r).den < B
      exact (hden r).trans_lt hM
    have heν : ν.vars "metric.entry" = r.val := by
      rw [hrow]
      exact (rindex.frame_var "metric.entry" (by decide)).trans hentry
    obtain ⟨τ,rread,pread⟩ := RamUnsignedBuffer.read_spec B "flow.dual" "metric.entry" qs r.val hr h2
      (by rw [hrow]; have := (edgeIndex n (u,v)).isLt; omega) hnq hdq (by decide) ν ⟨hctxν.2.2,heν⟩
    have hv : ¬u.val = v.val := fun h => huv (Fin.ext h)
    have rbranch := Run.ite_false (c := RamFractionPrimitives.zero) (by simpa only [hv,decide_false] using hcond) rread
    refine ⟨τ,rindex.seq rbranch,frame rread hctxν (by decide) (by decide),?_⟩
    simpa only [matrix,RationalDistances.zeroDiagonal,if_neg huv,hqr,DirectedFlowDual.length,r] using pread.1

def build : Com := RamUnsignedVector.command "metric.entry" "metric.n2" "metric.old" "metric.position" coefficient

def setup : Com := .seq (.assign "metric.n" (.var "lp.n"))
  (.seq (.assign "metric.n2" (.var "lp.n2")) (.assign "metric.position" (.lit 0)))

def command : Com := .seq setup build

/-- Read the complete initial distance matrix from the decoded LP dual.
Graph dimensions come from the parsed source registers. -/
theorem command_spec (B M : ℕ) {n : ℕ} (y : Fin (RamFlowData.rows n) → ℚ) (hy : ∀ i, 0 ≤ y i)
    (h2 : 2 < B) (hM : M < B) (hn : n < B) (hn2 : n*n < B) (hindex : 2*(n*n)+2 < B)
    (hnum : ∀ i, (y i).num.natAbs ≤ M) (hden : ∀ i, (y i).den ≤ M) :
    Spec B (fun σ => σ.vars "lp.n" = n ∧ σ.vars "lp.n2" = n*n ∧
      Prefix (RamUnsignedBuffer.encode (RamOptimalDecode.vector y hy)) "flow.dual" σ ∧
      2*(n*n) < (σ.arrs "metric.old").length) command
      (fun _ τ => Context y hy τ ∧ Prefix (RamUnsignedBuffer.encode (values (matrix y hy))) "metric.old" τ)
      (50*(n*n)+12) := by
  let qs := values (matrix y hy)
  have hlength : qs.length = n*n := length_values _
  have hvals : ∀ i, ∀ hi : i < qs.length, qs[i].num < B ∧ qs[i].den < B := by
    intro i hi
    let uv := (edgeIndex n).symm (⟨i,by rwa [hlength] at hi⟩ : Fin (n*n))
    have hq : qs[i] = matrix y hy uv.1 uv.2 := by simp only [qs,values,List.getElem_ofFn,uv]
    rw [hq]
    unfold matrix RationalDistances.zeroDiagonal
    split_ifs
    · change NNRat.num (0 : ℚ≥0) < B ∧ NNRat.den (0 : ℚ≥0) < B
      simp; omega
    · change (DirectedFlowDual.length y uv.1 uv.2).num.natAbs < B ∧
        (DirectedFlowDual.length y uv.1 uv.2).den < B
      exact ⟨(hnum _).trans_lt hM,(hden _).trans_lt hM⟩
  have hloop := RamUnsignedVector.command_spec B 28 (Context y hy)
    "metric.entry" "metric.n2" "metric.old" "metric.position" qs [] coefficient (by omega)
    (by simp only [List.length_nil,hlength]; omega)
    (fun i hi => (hvals i hi).1) (fun i hi => (hvals i hi).2)
    (fun σ h => by simpa only [hlength] using h.2.1)
    (fun σ k h => by simpa only [Context,Prefix,vars_setVar,arrs_setVar,String.reduceEq,if_false] using h)
    (fun i hi => by
      have he : i < n*n := by rwa [hlength] at hi
      let uv := (edgeIndex n).symm (⟨i,he⟩ : Fin (n*n))
      have hidx : edgeIndex n uv = (⟨i,he⟩ : Fin (n*n)) := (edgeIndex n).apply_symm_apply _
      simpa only [hidx,qs,values,List.getElem_ofFn,uv,Fin.eta] using
        coefficient_spec B M y hy uv.1 uv.2 h2 hM hn hn2 (by omega) hnum hden)
    (by decide) (by decide) (by decide) (by decide)
    (fun hr h => frame hr h (by decide) (by decide)) (by decide) (by decide)
  rintro σ ⟨hN,hN2,hdual,hroom⟩
  let ν := ((σ.setVar "metric.n" n).setVar "metric.n2" (n*n)).setVar "metric.position" 0
  have rN : Run B (.assign "metric.n" (.var "lp.n")) σ (σ.setVar "metric.n" n) 2 :=
    Run.assign (by rw [evalB_var_iff]; exact ⟨hN.symm,hN ▸ hn⟩)
  have rN2 : Run B (.assign "metric.n2" (.var "lp.n2")) (σ.setVar "metric.n" n)
      ((σ.setVar "metric.n" n).setVar "metric.n2" (n*n)) 2 :=
    Run.assign (by rw [evalB_var_iff]; simpa only [vars_setVar,String.reduceEq,if_false]
      using And.intro hN2.symm (hN2 ▸ hn2))
  have rPos : Run B (.assign "metric.position" (.lit 0)) ((σ.setVar "metric.n" n).setVar "metric.n2" (n*n)) ν 2 :=
    Run.assign (evalB_lit (by omega))
  have hsetup := rN.seq (rN2.seq rPos)
  have hctxν : Context y hy ν := by
    refine ⟨by simp [ν],by simp [ν],?_⟩
    simpa only [Prefix,ν,arrs_setVar] using hdual
  obtain ⟨τ,hr,hpost⟩ := hloop ν ⟨hctxν,by intro i hi; simp at hi,by simp [ν],
    by simpa only [ν,arrs_setVar,hlength,List.length_nil,Nat.zero_add] using hroom⟩
  refine ⟨τ,?_,hpost.1,?_⟩
  · have rtotal := hsetup.seq hr
    exact rtotal.mono (by simp only [hlength,Nat.reduceAdd]; omega)
  · simpa only [qs,List.nil_append] using hpost.2.1

end Lax455465Proofs.RamDualDistancesInit
