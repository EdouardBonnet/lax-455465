import Lax455465Proofs.RamRadiusSearch

set_option maxRecDepth 4096
namespace Lax455465Proofs.RamSelectedRegion
open RadiusSearchData RamRadiusSearch RegionQueryData Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open scoped NNRat

def restore : Com := .seq (.assign "find.i" (.var "find.result")) RamRadiusSearch.test

def command : Com := .seq RamRadiusSearch.command
  (.ite (.eq (.var "find.found") (.lit 1)) restore .skip)

def Selected {n : ℕ} (q : Query n) (radii : List ℚ≥0) (σ : Env) : Prop :=
  match RamFind.first (predicate q radii) radii.length with
  | none => True
  | some i => Answer (atRadius q (radii.getD i 0)) σ

set_option maxHeartbeats 2400000 in
/-- After the native first-match scan, reload and evaluate the recorded
radius so the masks, orientation, boundary and volume all describe the
selected region. The no-success branch terminates without a query. -/
theorem command_spec (B H : ℕ) {n : ℕ} (q : Query n) (radii : List ℚ≥0)
    (hb : ∀ i, ∀ hi : i<radii.length, RegionQueryHeight.Bounds (atRadius q radii[i]) H)
    (hB : 2*(2^H)^2+3 < B) (hindex : 2*(n*n)+2 < B) (hvertex : 2*n+2 < B)
    (hposition : 2*radii.length+2 < B) :
    Spec B (Context q radii) command
      (fun _ τ => Context q radii τ ∧ RamFind.Matches
        (RamFind.first (predicate q radii) radii.length) τ ∧ Selected q radii τ)
      ((queryCost n H+38)*radii.length+queryCost n H+40) := by
  rintro σ hσ
  obtain ⟨ν,rs,ps⟩ := RamRadiusSearch.command_spec B H q radii hb hB hindex hvertex hposition σ hσ
  cases hs : RamFind.first (predicate q radii) radii.length with
  | none =>
    have hm : ν.vars "find.found"=0 := by simpa only [hs,RamFind.Matches] using ps.2
    have hc : (Cond.eq (.var "find.found") (.lit 1)).evalB B ν = some false := by
      rw [evalB_condEq (evalB_var (hm ▸ (by omega : 0<B))) (evalB_lit (by omega)),hm]
      rfl
    refine ⟨ν,(rs.seq (Run.ite_false (c := restore) hc Run.skip)).mono (by dsimp [Cond.size,Expr.size]; omega),ps.1,by simpa only [hs] using ps.2,?_⟩
    simp only [Selected,hs]
  | some i =>
    have hi := (RamFind.first_some (predicate q radii) radii.length i hs).1
    have hm : ν.vars "find.found"=1 ∧ ν.vars "find.result"=i := by simpa only [hs,RamFind.Matches] using ps.2
    have hc : (Cond.eq (.var "find.found") (.lit 1)).evalB B ν = some true := by
      rw [evalB_condEq (evalB_var (hm.1 ▸ (by omega : 1<B))) (evalB_lit (by omega)),hm.1]
      rfl
    let μ := ν.setVar "find.i" i
    have ra : Run B (.assign "find.i" (.var "find.result")) ν μ 2 :=
      Run.assign (by rw [evalB_var_iff]; exact ⟨hm.2.symm,hm.2 ▸ (by omega : i<B)⟩)
    obtain ⟨τ,rq,pq⟩ := test_answer_spec B H q radii i hi (hb i hi) hB hindex hvertex (by omega) μ
      ⟨setFinder ps.1 i "find.i" (by simp),by simp [μ]⟩
    have rr := ra.seq rq
    refine ⟨τ,(rs.seq (Run.ite_true (d := Com.skip) hc rr)).mono (by dsimp [Cond.size,Expr.size]; omega),pq.1,?_,?_⟩
    · simpa only [hs,RamFind.Matches,rr.frame_var "find.found" (by decide),rr.frame_var "find.result" (by decide)] using hm
    · simpa only [Selected,hs,List.getD_eq_get radii 0 (⟨i,hi⟩ : Fin radii.length),List.get_eq_getElem] using pq.2

end Lax455465Proofs.RamSelectedRegion
