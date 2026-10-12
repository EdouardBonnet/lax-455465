import Lax455465Proofs.RamRegionRecord

namespace Lax455465Proofs.RamHistoryEntry
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar RamRegionRecord
open scoped NNRat

theorem word_at {n : ℕ} (history : List (Entry n)) (i : ℕ) (hi : i < history.length) (j : Fin 4) :
    (words history)[4*i+j.val]? = some (history[i].words[j.val]'(by simp [Entry.words])) := by
  induction history generalizing i with
  | nil => simp at hi
  | cons e rest ih =>
    cases i with
    | zero => fin_cases j <;> simp [words,Entry.words]
    | succ i =>
      have hr : i < rest.length := by simpa using hi
      simpa only [words,List.flatMap_cons,Entry.words,List.cons_append,List.nil_append,
        show 4*(i+1)+j.val=Nat.succ (Nat.succ (Nat.succ (Nat.succ (4*i+j.val)))) by omega,
        List.getElem?_cons_succ,List.getElem_cons_succ] using ih i hr

def command : Com := .seq (.assign "history.address" (.mul (.lit 4) (.var "find.i")))
  (.seq (.assign "history.root" (.get "region.history" (.var "history.address")))
    (.seq (.assign "history.radius.n" (.get "region.history" (.add (.var "history.address") (.lit 1))))
      (.seq (.assign "history.radius.d" (.get "region.history" (.add (.var "history.address") (.lit 2))))
        (.assign "history.outward" (.get "region.history" (.add (.var "history.address") (.lit 3)))))))

def Output {n : ℕ} (e : Entry n) (σ : Env) : Prop :=
  σ.vars "history.root"=e.root.val ∧ Stored "history.radius" e.radius σ ∧
    σ.vars "history.outward"=(if e.outward then 1 else 0)

/-- Decode one actual four-word region record without changing the history. -/
theorem command_spec (B : ℕ) {n : ℕ} (history : List (Entry n)) (i : ℕ) (hi : i < history.length)
    (h4 : 4 < B) (hlen : 4*history.length < B) (hn : n < B)
    (hnum : history[i].radius.num < B) (hden : history[i].radius.den < B) :
    Spec B (fun σ => Prefix (words history) "region.history" σ ∧ σ.vars "find.i"=i) command
      (fun _ τ => Output history[i] τ) 22 := by
  rintro σ ⟨hp,hiσ⟩
  have hg : ∀ j : Fin 4, (σ.arrs "region.history")[4*i+j.val]?=some (history[i].words[j.val]'(by simp [Entry.words])) := by
    intro j
    have hj : 4*i+j.val < (words history).length := by simp only [length_words]; omega
    exact (hp _ hj).trans ((List.getElem?_eq_getElem hj).symm.trans (word_at history i hi j))
  have hg0 := hg 0
  have hg1 := hg 1
  have hg2 := hg 2
  have hg3 := hg 3
  simp only [Entry.words,Fin.val_zero,Fin.val_one,Fin.val_two,Nat.add_zero,
    List.getElem_cons_zero,List.getElem_cons_succ] at hg0 hg1 hg2 hg3
  have hroom : 4*i+3 < (σ.arrs "region.history").length := List.getElem?_eq_some_iff.mp hg3 |>.1
  have hr : history[i].root.val < B := history[i].root.isLt.trans hn
  have ho : (if history[i].outward then 1 else 0) < B := by split_ifs <;> omega
  have hiB : i < B := by omega
  have hbase : 4*i < B := by omega
  have ha1 : 4*i+1 < B := by omega
  have ha2 : 4*i+2 < B := by omega
  have ha3 : 4*i+3 < B := by omega
  run_vcg
  all_goals simp_all [Output,Stored]

end Lax455465Proofs.RamHistoryEntry
