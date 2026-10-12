/-
Generic RAM layout utility reused from the registered LP development, Apache-2.0:
https://github.com/EdouardBonnet/lax-109476/tree/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864
Only namespaces and imports are adapted here. The LP solver itself is used
through its registered concept theorem, rather than its proof package.
-/
import Lax455465Proofs.RamTransfer
import Mathlib.Tactic

namespace Lax455465Proofs.RamAutomaticLayout

open Lax808846Proofs.Imp Lax808846Proofs.Compile

def expressionNames : Expr → List String × List String
  | .lit _ => ([], [])
  | .var x => ([x], [])
  | .get a i => let old := expressionNames i; (old.1, a :: old.2)
  | .bin _ e f => let a := expressionNames e; let b := expressionNames f; (a.1 ++ b.1, a.2 ++ b.2)

def conditionNames (b : Cond) : List String × List String := expressionNames (condExpr b)

def commandNames : Com → List String × List String
  | .skip => ([], [])
  | .assign x e => let a := expressionNames e; (x :: a.1, a.2)
  | .store x i e => let a := expressionNames i; let b := expressionNames e; (a.1 ++ b.1, x :: (a.2 ++ b.2))
  | .seq c d => let a := commandNames c; let b := commandNames d; (a.1 ++ b.1, a.2 ++ b.2)
  | .ite b c d => let a := conditionNames b; let x := commandNames c; let y := commandNames d;
      (a.1 ++ x.1 ++ y.1, a.2 ++ x.2 ++ y.2)
  | .while b c => let a := conditionNames b; let x := commandNames c; (a.1 ++ x.1, a.2 ++ x.2)
  | .read x => ([x], [])
  | .write e => expressionNames e

def commandDepth : Com → ℕ
  | .skip | .read _ => 1
  | .assign _ e | .write e => e.size + 2
  | .store _ i e => max i.size e.size + 2
  | .seq c d => max (commandDepth c) (commandDepth d)
  | .ite b c d => max (condExpr b).size (max (commandDepth c) (commandDepth d)) + 2
  | .while b c => max (condExpr b).size (commandDepth c) + 2

def layout (c : Com) : Layout := ⟨(commandNames c).1, (commandNames c).2, commandDepth c + 2⟩

theorem expression_ok (e : Expr) (L : Layout) (d : ℕ)
    (hv : (expressionNames e).1 ⊆ L.scalars) (ha : (expressionNames e).2 ⊆ L.arrays)
    (hd : d + e.size < L.temps) : Expr.Ok L e d := by
  induction e generalizing d with
  | lit v => trivial
  | var x => exact hv (by simp [expressionNames])
  | get a i ih =>
    refine ⟨ha (by simp [expressionNames]), ih d
      (by simpa [expressionNames] using hv)
      (fun x hx => ha (by simp [expressionNames, hx])) ?_, ?_⟩
    all_goals simp only [Expr.size] at hd; omega
  | bin op e f ihe ihf =>
    have hve : (expressionNames e).1 ⊆ L.scalars := fun x hx => hv (by simp [expressionNames, hx])
    have hvf : (expressionNames f).1 ⊆ L.scalars := fun x hx => hv (by simp [expressionNames, hx])
    have hae : (expressionNames e).2 ⊆ L.arrays := fun x hx => ha (by simp [expressionNames, hx])
    have haf : (expressionNames f).2 ⊆ L.arrays := fun x hx => ha (by simp [expressionNames, hx])
    simp only [Expr.Ok]
    exact ⟨ihf d hvf haf (by simp only [Expr.size] at hd; omega),
      ihe (d + 1) hve hae (by simp only [Expr.size] at hd; omega),
      by simp only [Expr.size] at hd; omega⟩

theorem command_ok (c : Com) (L : Layout)
    (hv : (commandNames c).1 ⊆ L.scalars) (ha : (commandNames c).2 ⊆ L.arrays)
    (hd : commandDepth c < L.temps) : Com.Ok L c := by
  induction c with
  | skip => trivial
  | read x => exact hv (by simp [commandNames])
  | assign x e =>
    refine ⟨hv (by simp [commandNames]), expression_ok e L 0
      (fun x hx => hv (by simp [commandNames, hx])) (by simpa [commandNames] using ha) ?_⟩
    simp only [commandDepth] at hd; omega
  | store a i e =>
    refine ⟨ha (by simp [commandNames]), expression_ok i L 0
      (fun x hx => hv (by simp [commandNames, hx])) (fun x hx => ha (by simp [commandNames, hx])) ?_,
      expression_ok e L 1 (fun x hx => hv (by simp [commandNames, hx]))
        (fun x hx => ha (by simp [commandNames, hx])) ?_, ?_⟩
    all_goals simp only [commandDepth] at hd; omega
  | write e =>
    refine ⟨expression_ok e L 0 hv ha ?_, ?_⟩
    all_goals simp only [commandDepth] at hd; omega
  | seq c d ihc ihd =>
    refine ⟨ihc (fun x hx => hv (by simp [commandNames, hx]))
      (fun x hx => ha (by simp [commandNames, hx])) ?_,
      ihd (fun x hx => hv (by simp [commandNames, hx]))
        (fun x hx => ha (by simp [commandNames, hx])) ?_⟩
    all_goals simp only [commandDepth] at hd; omega
  | ite b c d ihc ihd =>
    refine ⟨expression_ok (condExpr b) L 0
      (fun x hx => hv (by simp [commandNames, conditionNames, hx]))
      (fun x hx => ha (by simp [commandNames, conditionNames, hx])) ?_,
      ihc (fun x hx => hv (by simp [commandNames, hx])) (fun x hx => ha (by simp [commandNames, hx])) ?_,
      ihd (fun x hx => hv (by simp [commandNames, hx])) (fun x hx => ha (by simp [commandNames, hx])) ?_⟩
    all_goals simp only [commandDepth] at hd; omega
  | «while» b c ih =>
    refine ⟨expression_ok (condExpr b) L 0
      (fun x hx => hv (by simp [commandNames, conditionNames, hx]))
      (fun x hx => ha (by simp [commandNames, conditionNames, hx])) ?_,
      ih (fun x hx => hv (by simp [commandNames, hx])) (fun x hx => ha (by simp [commandNames, hx])) ?_⟩
    all_goals simp only [commandDepth] at hd; omega

theorem layout_ok (c : Com) : Com.Ok (layout c) c :=
  command_ok c (layout c) (fun _ h => h) (fun _ h => h) (by simp [layout])

end Lax455465Proofs.RamAutomaticLayout
