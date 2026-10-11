import Lax455465Proofs.RootData
import Lax455465Proofs.RamUnsignedBuffer

namespace Lax455465Proofs.RamRoot

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamRational
open scoped NNRat

def test : Com := .seq (RamUnsignedBuffer.read "region.weights" "find.i")
  (.ite (.eq (.var "rat.n") (.lit 0)) (.assign "find.ok" (.lit 0)) (.assign "find.ok" (.lit 1)))

theorem test_spec (B : ℕ) (qs : List ℚ≥0) (i : ℕ) (hi : i < qs.length)
    (h2 : 2 < B) (hindex : 2*i+1 < B) (hnum : qs[i].num < B) (hden : qs[i].den < B) :
    Spec B (fun σ => Prefix (RamUnsignedBuffer.encode qs) "region.weights" σ ∧ σ.vars "find.i"=i)
      test (fun _ τ => τ.vars "find.ok" = if RootData.predicate qs i then 1 else 0) 20 := by
  intro σ hσ
  obtain ⟨ν,rr,pr⟩ := RamUnsignedBuffer.read_spec B "region.weights" "find.i" qs i hi h2 hindex hnum hden (by decide) σ hσ
  have hn : ν.vars "rat.n" = qs[i].num := by simpa only [NNRat.natAbs_num_coe] using pr.1.2.1
  have hc : (Cond.eq (.var "rat.n") (.lit 0)).evalB B ν = some (decide (qs[i].num=0)) := by
    rw [evalB_condEq (evalB_var (hn ▸ hnum)) (evalB_lit (by omega)),hn]
    rfl
  by_cases hz : qs[i].num=0
  · have rb : Run B (.assign "find.ok" (.lit 0)) ν (ν.setVar "find.ok" 0) 2 := Run.assign (evalB_lit (by omega))
    refine ⟨ν.setVar "find.ok" 0,(rr.seq (Run.ite_true (d := .assign "find.ok" (.lit 1)) (by simpa only [hz,decide_true] using hc) rb)).mono (by dsimp [Cond.size,Expr.size]; omega),?_⟩
    simp only [vars_setVar,if_pos rfl,RootData.predicate,List.getD_eq_get qs 0 (⟨i,hi⟩ : Fin qs.length),List.get_eq_getElem,hz]
    rfl
  · have rb : Run B (.assign "find.ok" (.lit 1)) ν (ν.setVar "find.ok" 1) 2 := Run.assign (evalB_lit (by omega))
    refine ⟨ν.setVar "find.ok" 1,(rr.seq (Run.ite_false (c := .assign "find.ok" (.lit 0)) (by simpa only [hz,decide_false] using hc) rb)).mono (by dsimp [Cond.size,Expr.size]; omega),?_⟩
    simp only [vars_setVar,if_pos rfl,RootData.predicate,List.getD_eq_get qs 0 (⟨i,hi⟩ : Fin qs.length),List.get_eq_getElem,decide_eq_true (Nat.pos_of_ne_zero hz),if_true]

def Context {n : ℕ} (weights : Fin n → ℚ≥0) (σ : Env) : Prop :=
  σ.vars "metric.n"=n ∧ σ.vars "find.count"=n ∧
    Prefix (RamUnsignedBuffer.encode (List.ofFn weights)) "region.weights" σ

def command : Com := .seq (.assign "find.count" (.var "metric.n")) (RamFind.command test)

/-- Select the first currently positive-weight vertex using the actual
residual weight buffer. Zero-weight transit vertices are skipped as roots. -/
theorem command_spec (B H : ℕ) {n : ℕ} (weights : Fin n → ℚ≥0) (h2 : 2 < B)
    (hH : H < B) (hindex : 2*n+2 < B)
    (hnum : ∀ v, (weights v).num ≤ H) (hden : ∀ v, (weights v).den ≤ H) :
    Spec B (fun σ => σ.vars "metric.n"=n ∧ Prefix (RamUnsignedBuffer.encode (List.ofFn weights)) "region.weights" σ)
      command (fun _ τ => Context weights τ ∧ RamFind.Matches
        ((RegionSelection.chooseRoot (fun v => (weights v : ℚ))).map Fin.val) τ) (40*n+12) := by
  let qs := List.ofFn weights
  have hlen : qs.length=n := List.length_ofFn
  have hb : ∀ i, i < n → Spec B (fun σ => Context weights σ ∧ σ.vars "find.i"=i) test
      (fun _ τ => Context weights τ ∧ τ.vars "find.ok"=if RootData.predicate qs i then 1 else 0) 20 := by
    intro i hi σ hσ
    have hq : i < qs.length := by rwa [hlen]
    have he : qs[i] = weights ⟨i,hi⟩ := by simp only [qs,List.getElem_ofFn]
    obtain ⟨τ,rr,pr⟩ := test_spec B qs i hq h2 (by omega)
      (by rw [he]; exact (hnum _).trans_lt hH) (by rw [he]; exact (hden _).trans_lt hH) σ ⟨hσ.1.2.2,hσ.2⟩
    refine ⟨τ,rr,?_,pr⟩
    simpa only [Context,Prefix,rr.frame_var "metric.n" (by decide),rr.frame_var "find.count" (by decide),
      rr.frame_arr "region.weights" (by decide)] using hσ.1
  have hf := RamFind.command_spec B n 20 (Context weights) (RootData.predicate qs) test (by omega) (by omega)
    (fun _ h => h.2.1)
    (fun σ k name hσ hn => by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hn
      rcases hn with rfl|rfl|rfl <;> simpa only [Context,Prefix,vars_setVar,arrs_setVar,String.reduceEq,if_false] using hσ)
    hb (by decide)
  rintro σ ⟨hn,hprefix⟩
  let ν := σ.setVar "find.count" n
  have rstart : Run B (.assign "find.count" (.var "metric.n")) σ ν 2 :=
    Run.assign (by rw [evalB_var_iff]; exact ⟨hn.symm,hn ▸ (by omega : n < B)⟩)
  obtain ⟨τ,rr,pr⟩ := hf ν ⟨by simpa only [ν,vars_setVar,String.reduceEq,if_false] using hn,
    by simp [ν],by simpa only [ν,Prefix,arrs_setVar] using hprefix⟩
  refine ⟨τ,(rstart.seq rr).mono (by omega),pr.1,?_⟩
  simpa only [qs,RootData.first_eq] using pr.2

end Lax455465Proofs.RamRoot
