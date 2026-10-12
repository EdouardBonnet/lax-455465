import Lax455465Proofs.RamLayeredArcRead
import Lax455465Proofs.RamFind

namespace Lax455465Proofs.RamPositiveNext
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamRational LayeredFlowLP
open scoped NNRat

structure Context {n L : ℕ} (qs : Fin (1+(n*n)*(L*(n*n))) → ℚ≥0)
    (st : Edge n) (k : Fin L) (u : Fin n) (σ : Env) : Prop where
  order : σ.vars "lp.n"=n
  square : σ.vars "lp.n2"=n*n
  layerArcs : σ.vars "short.layerArcs"=L*(n*n)
  commodity : σ.vars "short.commodity"=(DirectedFlowLP.edgeIndex n st).val
  level : σ.vars "short.level"=k.val
  vertex : σ.vars "short.vertex"=u.val
  buffer : Prefix (RamUnsignedBuffer.encode (List.ofFn qs)) "flow.primal" σ
  count : σ.vars "find.count"=n

def names : List String := ["lp.n","lp.n2","short.layerArcs","short.commodity","short.level","short.vertex","find.count"]

theorem frame {B K : ℕ} {c : Com} {σ τ : Env} (rr : Run B c σ τ K)
    {n L : ℕ} {qs : Fin (1+(n*n)*(L*(n*n))) → ℚ≥0} {st : Edge n} {k : Fin L} {u : Fin n}
    (h : Context qs st k u σ) (hx : ∀ x∈names,x∉c.wvars) (ha : "flow.primal"∉c.warrs) :
    Context qs st k u τ := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (rr.frame_var _ (hx _ (by simp [names]))).trans h.order
  · exact (rr.frame_var _ (hx _ (by simp [names]))).trans h.square
  · exact (rr.frame_var _ (hx _ (by simp [names]))).trans h.layerArcs
  · exact (rr.frame_var _ (hx _ (by simp [names]))).trans h.commodity
  · exact (rr.frame_var _ (hx _ (by simp [names]))).trans h.level
  · exact (rr.frame_var _ (hx _ (by simp [names]))).trans h.vertex
  · simpa only [Prefix,rr.frame_arr _ ha] using h.buffer
  · exact (rr.frame_var _ (hx _ (by simp [names]))).trans h.count

def flag : Com := .ite (.lt (.lit 0) (.var "rat.n"))
  (.assign "find.ok" (.lit 1)) (.assign "find.ok" (.lit 0))

theorem flag_spec (B : ℕ) (q : ℚ≥0) (h1 : 1<B) (hq : q.num<B) :
    Spec B (FractionOutput (q : ℚ)) flag
      (fun _ τ => τ.vars "find.ok"=if 0<q then 1 else 0) 6 := by
  intro σ hσ
  have hn : σ.vars "rat.n"=q.num := by simpa only [NNRat.natAbs_num_coe] using hσ.2.1
  run_vcg
  all_goals simp_all [NNRat.num_pos]

def test : Com := .seq RamLayeredArcRead.command flag

def predicate {n L : ℕ} (qs : Fin (1+(n*n)*(L*(n*n))) → ℚ≥0)
    (st : Edge n) (k : Fin L) (u : Fin n) (i : ℕ) : Bool :=
  if hi : i<n then decide (0<qs (variableIndex n L (.inr (st,(k,(u,⟨i,hi⟩)))))) else false

theorem test_spec (B : ℕ) {n L : ℕ} (qs : Fin (1+(n*n)*(L*(n*n))) → ℚ≥0)
    (st : Edge n) (k : Fin L) (u v : Fin n)
    (hsize : n+n*n+L*(n*n)+2*(1+(n*n)*(L*(n*n)))+4<B)
    (hnum : ∀ v,(qs (variableIndex n L (.inr (st,(k,(u,v)))))).num<B)
    (hden : ∀ v,(qs (variableIndex n L (.inr (st,(k,(u,v)))))).den<B) :
    Spec B (fun σ => Context qs st k u σ ∧ σ.vars "find.i"=v.val) test
      (fun _ τ => Context qs st k u τ ∧ τ.vars "find.ok"=
        if predicate qs st k u v.val then 1 else 0) 48 := by
  rintro σ ⟨hc,hi⟩
  obtain ⟨ν,rr,pr⟩ := RamLayeredArcRead.command_spec B qs st k u v hsize (hnum v) (hden v) σ
    ⟨hc.order,hc.square,hc.layerArcs,hc.commodity,hc.level,hc.vertex,hi,hc.buffer⟩
  have hcν := frame rr hc (by decide) (by decide)
  obtain ⟨τ,rf,pf⟩ := flag_spec B (qs (variableIndex n L (.inr (st,(k,(u,v)))))) (by omega) (hnum v) ν pr
  refine ⟨τ,(rr.seq rf).mono (by omega),frame rf hcν (by decide) (by decide),?_⟩
  simpa only [predicate,dif_pos v.isLt,Fin.eta,decide_eq_true_eq] using pf

def command : Com := RamFind.command test

/-- Scan physical vertices in their input order and return the first
positive residual arc. The existence assumption is supplied by conservation. -/
theorem command_spec (B : ℕ) {n L : ℕ} (qs : Fin (1+(n*n)*(L*(n*n))) → ℚ≥0)
    (st : Edge n) (k : Fin L) (u : Fin n)
    (hsize : n+n*n+L*(n*n)+2*(1+(n*n)*(L*(n*n)))+4<B)
    (hnum : ∀ v,(qs (variableIndex n L (.inr (st,(k,(u,v)))))).num<B)
    (hden : ∀ v,(qs (variableIndex n L (.inr (st,(k,(u,v)))))).den<B)
    (hexists : ∃ v,0<qs (variableIndex n L (.inr (st,(k,(u,v)))))) :
    Spec B (Context qs st k u) command
      (fun _ τ => Context qs st k u τ ∧ ∃ v : Fin n,
        τ.vars "find.found"=1 ∧ τ.vars "find.result"=v.val ∧
        0<qs (variableIndex n L (.inr (st,(k,(u,v)))))) (68*n+10) := by
  have hscan := RamFind.command_spec B n 48 (Context qs st k u) (predicate qs st k u) test
    (by omega) (by omega) (fun _ h => h.count)
    (by
      intro σ j name h hm
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
      rcases hm with rfl | rfl | rfl
      all_goals refine ⟨?_,?_,?_,?_,?_,?_,h.buffer,?_⟩
      all_goals first
        | simpa only [vars_setVar,String.reduceEq,if_false] using h.order
        | simpa only [vars_setVar,String.reduceEq,if_false] using h.square
        | simpa only [vars_setVar,String.reduceEq,if_false] using h.layerArcs
        | simpa only [vars_setVar,String.reduceEq,if_false] using h.commodity
        | simpa only [vars_setVar,String.reduceEq,if_false] using h.level
        | simpa only [vars_setVar,String.reduceEq,if_false] using h.vertex
        | simpa only [vars_setVar,String.reduceEq,if_false] using h.count)
    (fun i hi => by simpa only [Fin.eta] using test_spec B qs st k u ⟨i,hi⟩ hsize hnum hden) (by decide)
  intro σ hc
  obtain ⟨τ,rr,pr⟩ := hscan σ hc
  cases he : RamFind.first (predicate qs st k u) n with
  | none =>
    obtain ⟨v,hv⟩ := hexists
    have ht : predicate qs st k u v.val=true := by simp [predicate,v.isLt,hv]
    have hh := RamFind.first_none _ _ he v.val v.isLt
    rw [ht] at hh
    cases hh
  | some i =>
    obtain ⟨hi,hp⟩ := RamFind.first_some _ _ _ he
    have hv : 0<qs (variableIndex n L (.inr (st,(k,(u,⟨i,hi⟩))))) := by
      simpa only [predicate,dif_pos hi,decide_eq_true_eq] using hp
    have hm : τ.vars "find.found"=1 ∧ τ.vars "find.result"=i := by
      simpa only [he,RamFind.Matches] using pr.2
    exact ⟨τ,rr,pr.1,⟨⟨i,hi⟩,hm.1,hm.2,hv⟩⟩

end Lax455465Proofs.RamPositiveNext
