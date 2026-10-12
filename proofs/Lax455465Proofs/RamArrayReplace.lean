import Lax455465Proofs.UnsignedArray

namespace Lax455465Proofs.RamArrayReplace
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamRational UnsignedArray
open scoped NNRat

/-- Replace one canonical residual coordinate in place. -/
def command (array index : String) : Com :=
  .seq (.store array (.mul (.lit 2) (.var index)) (.var "rat.n"))
    (.store array (.add (.mul (.lit 2) (.var index)) (.lit 1)) (.var "rat.d"))

theorem command_spec (B : ℕ) {N : ℕ} (q : Fin N → ℚ≥0) (j : Fin N) (r : ℚ≥0)
    (array index : String) (hindex : 2*N+1<B) (hn : r.num<B) (hd : r.den<B) :
    Spec B (fun σ => Initialized q array σ ∧ σ.vars index=j.val ∧ FractionOutput (r : ℚ) σ)
      (command array index) (fun _ τ => Initialized (Function.update q j r) array τ) 12 := by
  rintro σ ⟨harray,hj,hfrac⟩
  have hnum : σ.vars "rat.n"=r.num := by simpa only [NNRat.natAbs_num_coe] using hfrac.2.1
  have hden : σ.vars "rat.d"=r.den := by simpa only [NNRat.den_coe] using hfrac.2.2.1
  have hroom : 2*j.val+1<(σ.arrs array).length := by
    by_contra hh
    have he := (harray j).2
    rw [List.getElem?_eq_none (by omega)] at he
    cases he
  have h2 : 2<B := by omega
  have h1 : 1<B := by omega
  have hjB : j.val<B := by omega
  have hmul : 2*j.val<B := by omega
  have hplus : 2*j.val+1<B := by omega
  let ν := σ.setArr array (2*j.val) r.num
  have ri : (Expr.var index).evalB B σ=some j.val := by
    rw [evalB_var_iff]
    exact ⟨hj.symm,hj ▸ hjB⟩
  have rn : Run B (.store array (.mul (.lit 2) (.var index)) (.var "rat.n")) σ ν 5 :=
    Run.store (evalB_bin (op := .mul) (evalB_lit h2) ri hmul)
      (by rw [evalB_var_iff]; exact ⟨hnum.symm,hnum ▸ hn⟩) (by omega)
  let τ := ν.setArr array (2*j.val+1) r.den
  have rd : Run B (.store array (.add (.mul (.lit 2) (.var index)) (.lit 1)) (.var "rat.d")) ν τ 7 :=
    Run.store (evalB_bin (op := .add)
      (evalB_bin (op := .mul) (evalB_lit h2) (by rw [evalB_var_iff]; exact ⟨by simpa only [ν,vars_setArr] using hj.symm,by simpa only [ν,vars_setArr] using hj ▸ hjB⟩) hmul)
      (evalB_lit h1) hplus)
      (by rw [evalB_var_iff]; exact ⟨by simpa only [ν,vars_setArr] using hden.symm,
        by simpa only [ν,vars_setArr] using hden ▸ hd⟩)
      (by simpa only [ν,arrs_setArr,if_true,List.length_set] using hroom)
  refine ⟨τ,rn.seq rd,?_⟩
  intro i
  by_cases he : i=j
  · subst i
    simp only [Initialized,Function.update_self,τ,ν,arrs_setArr,if_true]
    constructor
    · rw [List.getElem?_set_ne (by omega),List.getElem?_set_self (by omega)]
    · rw [List.getElem?_set_self (by simp only [List.length_set]; omega)]
  · have hne : i.val≠j.val := fun hh => he (Fin.ext hh)
    have hnew : Function.update q j r i=q i := Function.update_of_ne he _ _
    rw [hnew]
    constructor
    · simpa only [τ,ν,arrs_setArr,if_true,List.getElem?_set_ne (by omega : 2*j.val+1≠2*i.val),
        List.getElem?_set_ne (by omega : 2*j.val≠2*i.val)] using (harray i).1
    · simpa only [τ,ν,arrs_setArr,if_true,List.getElem?_set_ne (by omega : 2*j.val+1≠2*i.val+1),
        List.getElem?_set_ne (by omega : 2*j.val≠2*i.val+1)] using (harray i).2

end Lax455465Proofs.RamArrayReplace
