import Lax455465Proofs.RamFrames

namespace Lax455465Proofs.RamFind

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

def first (predicate : ℕ → Bool) (count : ℕ) : Option ℕ := (List.range count).find? predicate

def Matches (result : Option ℕ) (σ : Env) : Prop :=
  match result with
  | none => σ.vars "find.found" = 0
  | some i => σ.vars "find.found" = 1 ∧ σ.vars "find.result" = i

def record : Com := .seq (.assign "find.found" (.lit 1)) (.assign "find.result" (.var "find.i"))
def process (body : Com) : Com := .ite (.eq (.var "find.found") (.lit 0))
  (.seq body (.ite (.eq (.var "find.ok") (.lit 1)) record .skip)) .skip

def step (body : Com) : Com := .seq (process body) (.assign "find.i" (.add (.var "find.i") (.lit 1)))
def init : Com := .seq (.assign "find.found" (.lit 0)) (.assign "find.result" (.lit 0))
def command (body : Com) : Com := .seq init (.seq (.assign "find.i" (.lit 0))
  (.while (.lt (.var "find.i") (.var "find.count")) (step body)))

/-- The first-match semantics follows the order of the actual runtime scan. -/
theorem first_succ (predicate : ℕ → Bool) (i : ℕ) :
    first predicate (i+1) = match first predicate i with
      | some j => some j
      | none => if predicate i then some i else none := by
  simp only [first,List.range_succ,List.find?_append,List.find?_cons,List.find?_nil]
  cases h : (List.range i).find? predicate <;> cases predicate i <;> rfl

def Invariant (R : Env → Prop) (predicate : ℕ → Bool) (count : ℕ) (σ : Env) : Prop :=
  R σ ∧ σ.vars "find.i" ≤ count ∧ Matches (first predicate (σ.vars "find.i")) σ

set_option maxHeartbeats 800000 in
/-- A bounded native scan records the first successful test. The test is a
fixed native command; it is skipped after success while the counter finishes
its bounded scan. This supports both root and radius selection. -/
theorem command_spec (B count K : ℕ) (R : Env → Prop) (predicate : ℕ → Bool) (body : Com)
    (h1 : 1 < B) (hcount : count < B)
    (hlimit : ∀ σ, R σ → σ.vars "find.count" = count)
    (hset : ∀ σ k name, R σ → name ∈ ["find.i","find.found","find.result"] → R (σ.setVar name k))
    (hbody : ∀ i, i < count → Spec B (fun σ => R σ ∧ σ.vars "find.i" = i) body
      (fun _ τ => R τ ∧ τ.vars "find.ok" = if predicate i then 1 else 0) K)
    (hfresh : "find.i" ∉ body.wvars ∧ "find.found" ∉ body.wvars ∧ "find.result" ∉ body.wvars) :
    Spec B R (command body) (fun _ τ => R τ ∧ Matches (first predicate count) τ)
      ((K+20)*count+10) := by
  have hprocess : ∀ i, i < count →
      Spec B (fun σ => R σ ∧ σ.vars "find.i" = i ∧ Matches (first predicate i) σ)
        (process body) (fun _ τ => R τ ∧ τ.vars "find.i" = i ∧ Matches (first predicate (i+1)) τ) (K+12) := by
    intro i hi σ ⟨hR,hindex,hmatch⟩
    have hiB : i < B := hi.trans hcount
    cases hs : first predicate i with
    | some j =>
      have hm : σ.vars "find.found" = 1 ∧ σ.vars "find.result" = j := by simpa only [hs,Matches] using hmatch
      have hc : (Cond.eq (.var "find.found") (.lit 0)).evalB B σ = some false := by
        rw [evalB_condEq (evalB_var (hm.1 ▸ h1)) (evalB_lit (by omega)),hm.1]
        rfl
      refine ⟨σ,(Run.ite_false (c := .seq body (.ite (.eq (.var "find.ok") (.lit 1)) record .skip)) hc Run.skip).mono (by dsimp [Cond.size,Expr.size]; omega),hR,hindex,?_⟩
      rw [first_succ,hs]
      exact hm
    | none =>
      have hm : σ.vars "find.found" = 0 := by simpa only [hs,Matches] using hmatch
      have hc : (Cond.eq (.var "find.found") (.lit 0)).evalB B σ = some true := by
        rw [evalB_condEq (evalB_var (hm ▸ (by omega : 0 < B))) (evalB_lit (by omega)),hm]
        rfl
      obtain ⟨ν,rb,pb⟩ := hbody i hi σ ⟨hR,hindex⟩
      have hiν : ν.vars "find.i" = i := (rb.frame_var "find.i" hfresh.1).trans hindex
      have hmν : ν.vars "find.found" = 0 := (rb.frame_var "find.found" hfresh.2.1).trans hm
      cases hp : predicate i with
      | false =>
        have hok : ν.vars "find.ok" = 0 := by simpa only [hp,Bool.false_eq_true,if_false] using pb.2
        have hcok : (Cond.eq (.var "find.ok") (.lit 1)).evalB B ν = some false := by
          rw [evalB_condEq (evalB_var (hok ▸ (by omega : 0 < B))) (evalB_lit h1),hok]
          rfl
        have rr := Run.ite_true (d := Com.skip) hc (rb.seq (Run.ite_false (c := record) hcok Run.skip))
        refine ⟨ν,rr.mono (by dsimp [Cond.size,Expr.size]; omega),pb.1,hiν,?_⟩
        rw [first_succ,hs,hp]
        exact hmν
      | true =>
        have hok : ν.vars "find.ok" = 1 := by simpa only [hp,if_true] using pb.2
        have hcok : (Cond.eq (.var "find.ok") (.lit 1)).evalB B ν = some true := by
          rw [evalB_condEq (evalB_var (hok ▸ h1)) (evalB_lit h1),hok]
          rfl
        let τ := (ν.setVar "find.found" 1).setVar "find.result" i
        have rrecord : Run B record ν τ 4 := (Run.assign (evalB_lit h1)).seq
          (Run.assign (by rw [evalB_var_iff]; exact ⟨by simpa only [vars_setVar,String.reduceEq,if_false] using hiν.symm,
            by simpa only [vars_setVar,String.reduceEq,if_false] using hiν ▸ hiB⟩))
        have rr := Run.ite_true (d := Com.skip) hc (rb.seq (Run.ite_true (d := Com.skip) hcok rrecord))
        refine ⟨τ,rr.mono (by dsimp [Cond.size,Expr.size]; omega),?_,?_,?_⟩
        · exact hset _ i "find.result" (hset ν 1 "find.found" pb.1 (by simp)) (by simp)
        · simpa only [τ,vars_setVar,String.reduceEq,if_false] using hiν
        · rw [first_succ,hs,hp]
          simp [Matches,τ]
  have hstep : Spec B (fun σ => Invariant R predicate count σ ∧ σ.vars "find.i" < count)
      (step body) (fun σ τ => Invariant R predicate count τ ∧ τ.vars "find.i" = σ.vars "find.i"+1) (K+16) := by
    rintro σ ⟨⟨hR,hi,hmatch⟩,hlt⟩
    let i := σ.vars "find.i"
    obtain ⟨ν,rr,pr⟩ := hprocess i hlt σ ⟨hR,rfl,hmatch⟩
    have hiν : ν.vars "find.i" = i := pr.2.1
    have rinc : Run B (.assign "find.i" (.add (.var "find.i") (.lit 1))) ν (ν.setVar "find.i" (i+1)) 4 :=
      Run.assign (evalB_bin (op := .add) (by rw [evalB_var_iff]; exact ⟨hiν.symm,hiν ▸ (by omega : i < B)⟩)
        (evalB_lit h1) (by dsimp [Bop.apply]; omega))
    refine ⟨ν.setVar "find.i" (i+1),(rr.seq rinc).mono (by omega),?_,by simp [i]⟩
    refine ⟨hset ν (i+1) "find.i" pr.1 (by simp),by simp; omega,?_⟩
    change Matches (first predicate (i+1)) (ν.setVar "find.i" (i+1))
    cases h : first predicate (i+1) <;>
      simpa only [h,Matches,vars_setVar,String.reduceEq,if_false] using pr.2.2
  have hscan := Spec.forRangeZero "find.i" "find.count" (Invariant R predicate count) count (K+16)
    hcount (fun _ h => h.2.1) (fun σ h => hlimit σ h.1) hstep
  rintro σ hR
  let ν := (σ.setVar "find.found" 0).setVar "find.result" 0
  have rinit : Run B init σ ν 4 := (Run.assign (evalB_lit (by omega : 0 < B))).seq (Run.assign (evalB_lit (by omega)))
  have hRν : R ν := hset _ 0 "find.result" (hset σ 0 "find.found" hR (by simp)) (by simp)
  have hinvariant : Invariant R predicate count (ν.setVar "find.i" 0) := by
    refine ⟨hset ν 0 "find.i" hRν (by simp),by simp,?_⟩
    simp [first,Matches,ν]
  obtain ⟨τ,rr,pr⟩ := hscan ν hinvariant
  refine ⟨τ,(rinit.seq rr).mono (by simp only [Nat.add_assoc,Nat.reduceAdd]; omega),pr.1.1,?_⟩
  simpa only [pr.2] using pr.1.2.2

theorem first_some (predicate : ℕ → Bool) (count i : ℕ) (h : first predicate count = some i) :
    i < count ∧ predicate i = true := by
  exact ⟨List.mem_range.mp (List.mem_of_find?_eq_some h),List.find?_some h⟩

theorem first_none (predicate : ℕ → Bool) (count : ℕ) (h : first predicate count = none) :
    ∀ i < count, predicate i = false := by
  intro i hi
  exact Bool.eq_false_iff.mpr (List.find?_eq_none.mp h i (List.mem_range.mpr hi))

end Lax455465Proofs.RamFind
