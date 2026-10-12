import Lax455465Proofs.RamPathState

namespace Lax455465Proofs.RamPathEdgeRead
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamRational
open LayeredFlowLP RamPathState
open scoped NNRat

def Context {n L : ℕ} (qs : Fin (1+(n*n)*(L*(n*n))) → ℚ≥0) (st : Edge n)
    (path : Fin (L+1) → Fin n) (σ : Env) : Prop :=
  Data qs st σ ∧ Prefix (List.ofFn fun i => (path i).val) "short.raw" σ

def command : Com := .seq (.seq (.assign "short.vertex" (.get "short.raw" (.var "short.level")))
  (.assign "find.i" (.get "short.raw" (.add (.var "short.level") (.lit 1)))))
    RamLayeredArcRead.command

/-- Evaluate a raw path edge at its runtime layer counter, preserving
both the source primal buffer and the complete stored path. -/
theorem index_spec (B : ℕ) {n L : ℕ} (qs : Fin (1+(n*n)*(L*(n*n))) → ℚ≥0)
    (st : Edge n) (path : Fin (L+1) → Fin n) (k : Fin L)
    (hsize : n+n*n+L*(n*n)+2*(1+(n*n)*(L*(n*n)))+2*L+20<B)
    (hnum : ∀ j,(qs j).num<B) (hden : ∀ j,(qs j).den<B) :
    Spec B (fun σ => Context qs st path σ ∧ σ.vars "short.level"=k.val) command
      (fun _ τ => Context qs st path τ ∧ FractionOutput
        (qs (variableIndex n L (.inr (st,(k,(path k.castSucc,path k.succ))))) : ℚ) τ ∧
        τ.vars "short.arcIndex"=(variableIndex n L (.inr (st,(k,(path k.castSucc,path k.succ))))).val) 48 := by
  rintro σ ⟨⟨hd,hpath⟩,hk⟩
  have hnB : n<B := by omega
  have hL : L+1<B := by omega
  have hzero : 0<B := by omega
  have hi0 : k.val<(List.ofFn fun i => (path i).val).length := by simp only [List.length_ofFn]; omega
  have hi1 : k.val+1<(List.ofFn fun i => (path i).val).length := by simp only [List.length_ofFn]; omega
  have he0 : (List.ofFn fun i => (path i).val)[k.val]=(path k.castSucc).val := by
    rw [List.getElem_ofFn]
    rfl
  have he1 : (List.ofFn fun i => (path i).val)[k.val+1]=(path k.succ).val := by
    rw [List.getElem_ofFn]
    rfl
  have hget0 : (σ.arrs "short.raw")[k.val]?=some (path k.castSucc).val :=
    (hpath k.val hi0).trans (congrArg some he0)
  have hget1 : (σ.arrs "short.raw")[k.val+1]?=some (path k.succ).val :=
    (hpath (k.val+1) hi1).trans (congrArg some he1)
  have hroom0 : k.val<(σ.arrs "short.raw").length := by have hh:=hd.rawRoom; omega
  have hroom1 : k.val+1<(σ.arrs "short.raw").length := by have hh:=hd.rawRoom; omega
  have hv0 : (path k.castSucc).val<B := (path k.castSucc).isLt.trans hnB
  have hv1 : (path k.succ).val<B := (path k.succ).isLt.trans hnB
  let ν := (σ.setVar "short.vertex" (path k.castSucc).val).setVar "find.i" (path k.succ).val
  have rread : Run B (.seq (.assign "short.vertex" (.get "short.raw" (.var "short.level")))
      (.assign "find.i" (.get "short.raw" (.add (.var "short.level") (.lit 1))))) σ ν 8 := by
    suffices ∃ τ,Run B (.seq (.assign "short.vertex" (.get "short.raw" (.var "short.level")))
        (.assign "find.i" (.get "short.raw" (.add (.var "short.level") (.lit 1))))) σ τ 8 ∧ τ=ν by
      obtain ⟨τ,rr,rfl⟩:=this
      exact rr
    run_vcg
    all_goals simp_all [ν]
  have hdν := data_frame rread hd (by decide) (by decide)
  obtain ⟨τ,rr,pr⟩ := RamLayeredArcRead.index_spec B qs st k (path k.castSucc) (path k.succ) (by omega)
    (hnum _) (hden _) ν
    ⟨hdν.order,hdν.square,hdν.layerArcs,hdν.commodity,
      by simpa only [ν,vars_setVar,String.reduceEq,if_false] using hk,
      by simp [ν],by simp [ν],hdν.buffer⟩
  refine ⟨τ,rread.seq rr,⟨data_frame rr hdν (by decide) (by decide),?_⟩,pr⟩
  simpa only [Prefix,(rread.seq rr).frame_arr "short.raw" (by decide)] using hpath

theorem command_spec (B : ℕ) {n L : ℕ} (qs : Fin (1+(n*n)*(L*(n*n))) → ℚ≥0)
    (st : Edge n) (path : Fin (L+1) → Fin n) (k : Fin L)
    (hsize : n+n*n+L*(n*n)+2*(1+(n*n)*(L*(n*n)))+2*L+20<B)
    (hnum : ∀ j,(qs j).num<B) (hden : ∀ j,(qs j).den<B) :
    Spec B (fun σ => Context qs st path σ ∧ σ.vars "short.level"=k.val) command
      (fun _ τ => Context qs st path τ ∧ FractionOutput
        (qs (variableIndex n L (.inr (st,(k,(path k.castSucc,path k.succ))))) : ℚ) τ) 48 := by
  intro σ hσ
  obtain ⟨τ,rr,pr⟩ := index_spec B qs st path k hsize hnum hden σ hσ
  exact ⟨τ,rr,pr.1,pr.2.1⟩

end Lax455465Proofs.RamPathEdgeRead
