import Lax455465Proofs.LoopErasure
import Lax455465Proofs.RamFind
import Lax455465Proofs.RamWordBuffer

namespace Lax455465Proofs.RamCycleAppend
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState

def test : Com := .seq (.assign "erase.vertex" (.get "short.simple" (.var "find.i")))
  (.ite (.eq (.var "erase.vertex") (.var "short.vertex"))
    (.assign "find.ok" (.lit 1)) (.assign "find.ok" (.lit 0)))

def command : Com := .seq (.assign "find.count" (.var "short.simpleLength"))
  (.seq (RamFind.command test)
    (.ite (.eq (.var "find.found") (.lit 1))
      (.assign "short.simpleLength" (.add (.var "find.result") (.lit 1)))
      (RamWordBuffer.append "short.simple" "short.simpleLength" (.var "short.vertex"))))

def Context (xs : List ℕ) (v : ℕ) (σ : Env) : Prop :=
  Prefix xs "short.simple" σ ∧ σ.vars "short.simpleLength"=xs.length ∧
    σ.vars "short.vertex"=v ∧ xs.length<(σ.arrs "short.simple").length ∧
    σ.vars "find.count"=xs.length

def predicate (xs : List ℕ) (v i : ℕ) : Bool := decide (xs[i]?=some v)

theorem test_spec (B : ℕ) (xs : List ℕ) (v i : ℕ) (hi : i<xs.length)
    (hlen : xs.length<B) (hv : v<B) (hwords : ∀ x∈xs,x<B) (h1 : 1<B) :
    Spec B (fun σ => Context xs v σ ∧ σ.vars "find.i"=i) test
      (fun _ τ => Context xs v τ ∧ τ.vars "find.ok"=if predicate xs v i then 1 else 0) 9 := by
  have hx := hwords xs[i] (List.getElem_mem hi)
  rintro σ ⟨⟨hp,hsize,hvσ,hroom,hcount⟩,hiσ⟩
  have hget : (σ.arrs "short.simple")[i]?=some xs[i] := hp i hi
  have hiRoom : i<(σ.arrs "short.simple").length := hi.trans hroom
  run_vcg
  all_goals simp_all [Context,Prefix,predicate,List.getElem?_eq_getElem hi]

theorem prefix_take (xs : List ℕ) (k : ℕ) (σ : Env) (h : Prefix xs "short.simple" σ) :
    Prefix (xs.take k) "short.simple" σ := by
  intro i hi
  have hix : i<xs.length := by simp only [List.length_take] at hi; omega
  simpa only [List.getElem_take] using h i hix

/-- Native stack cycle erasure. Every truncation ends at the repeated
vertex; otherwise the current vertex is appended to the initialized buffer. -/
theorem command_spec (B : ℕ) (xs : List ℕ) (v : ℕ) (hdup : xs.Nodup)
    (hlen : xs.length+1<B) (hv : v<B) (hwords : ∀ x∈xs,x<B) (h1 : 1<B) :
    Spec B (fun σ => Prefix xs "short.simple" σ ∧ σ.vars "short.simpleLength"=xs.length ∧
      σ.vars "short.vertex"=v ∧ xs.length<(σ.arrs "short.simple").length) command
      (fun _ τ => Prefix (LoopErasure.append xs v) "short.simple" τ ∧
        τ.vars "short.simpleLength"=(LoopErasure.append xs v).length)
      (32*xs.length+40) := by
  have hscan := RamFind.command_spec B xs.length 9 (Context xs v) (predicate xs v) test h1 (by omega)
    (fun _ h => h.2.2.2.2)
    (by
      intro σ k name h hm
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
      rcases hm with rfl | rfl | rfl
      all_goals simpa only [Context,Prefix,vars_setVar,arrs_setVar,String.reduceEq,if_false] using h)
    (fun i hi => test_spec B xs v i hi (by omega) hv hwords h1) (by decide)
  rintro σ ⟨hp,hsize,hvσ,hroom⟩
  let ν := σ.setVar "find.count" xs.length
  have rcount : Run B (.assign "find.count" (.var "short.simpleLength")) σ ν 2 :=
    Run.assign (by rw [evalB_var_iff]; exact ⟨hsize.symm,hsize ▸ (by omega : xs.length<B)⟩)
  have hν : Context xs v ν := by
    refine ⟨hp,?_,?_,hroom,by simp [ν]⟩
    · simpa only [ν,vars_setVar,String.reduceEq,if_false] using hsize
    · simpa only [ν,vars_setVar,String.reduceEq,if_false] using hvσ
  obtain ⟨μ,rs,ps⟩ := hscan ν hν
  cases hs : RamFind.first (predicate xs v) xs.length with
  | some i =>
    obtain ⟨hi,hit⟩ := RamFind.first_some _ _ _ hs
    have helem : xs[i]=v := by
      simpa only [predicate,decide_eq_true_eq,List.getElem?_eq_getElem hi,Option.some.injEq] using hit
    have hm : μ.vars "find.found"=1 ∧ μ.vars "find.result"=i := by
      simpa only [hs,RamFind.Matches] using ps.2
    have hidx : xs.idxOf v=i := by
      rw [←helem]
      exact hdup.idxOf_getElem i hi
    have hmem : v∈xs := by rw [←helem]; exact List.getElem_mem hi
    have happ : LoopErasure.append xs v=xs.take (i+1) := by simp [LoopErasure.append,hmem,hidx]
    have hc : (Cond.eq (.var "find.found") (.lit 1)).evalB B μ=some true := by
      rw [evalB_condEq (evalB_var (hm.1 ▸ h1)) (evalB_lit h1),hm.1]
      rfl
    let τ := μ.setVar "short.simpleLength" (i+1)
    have rr : Run B (.assign "short.simpleLength" (.add (.var "find.result") (.lit 1))) μ τ 4 :=
      Run.assign (evalB_bin (op := .add)
        (by rw [evalB_var_iff]; exact ⟨hm.2.symm,hm.2 ▸ (by omega : i<B)⟩)
        (evalB_lit h1) (by dsimp [Bop.apply]; omega))
    refine ⟨τ,(rcount.seq (rs.seq (Run.ite_true (d := RamWordBuffer.append "short.simple" "short.simpleLength" (.var "short.vertex")) hc rr))).mono
      (by dsimp [Cond.size,Expr.size]; omega),?_,?_⟩
    · rw [happ]
      exact prefix_take xs (i+1) τ (by simpa only [Prefix,τ,arrs_setVar] using ps.1.1)
    · rw [happ]
      simp only [τ,vars_setVar,if_true,List.length_take,Nat.min_eq_left (by omega : i+1≤xs.length)]
  | none =>
    have hm : μ.vars "find.found"=0 := by simpa only [hs,RamFind.Matches] using ps.2
    have hnot : v∉xs := by
      intro hvxs
      obtain ⟨i,hi,he⟩ := List.getElem_of_mem hvxs
      have ht : predicate xs v i=true := by simp [predicate,List.getElem?_eq_getElem hi,he]
      have hh := RamFind.first_none _ _ hs i hi
      rw [ht] at hh
      cases hh
    have hc : (Cond.eq (.var "find.found") (.lit 1)).evalB B μ=some false := by
      rw [evalB_condEq (evalB_var (hm ▸ (by omega : 0<B))) (evalB_lit h1),hm]
      rfl
    obtain ⟨τ,rr,pr⟩ := RamWordBuffer.append_spec B "short.simple" "short.simpleLength" xs v
      (.var "short.vertex") h1 hlen μ ⟨ps.1.1,ps.1.2.1,ps.1.2.2.2.1,
        by rw [evalB_var_iff]; exact ⟨ps.1.2.2.1.symm,ps.1.2.2.1 ▸ hv⟩⟩
    refine ⟨τ,(rcount.seq (rs.seq (Run.ite_false (c := .assign "short.simpleLength" (.add (.var "find.result") (.lit 1))) hc rr))).mono
      (by dsimp [Cond.size,Expr.size]; omega),?_,?_⟩
    · simpa only [LoopErasure.append,if_neg hnot] using pr.1
    · simpa only [LoopErasure.append,if_neg hnot,List.length_append,List.length_singleton] using pr.2

end Lax455465Proofs.RamCycleAppend
