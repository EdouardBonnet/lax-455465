import Lax455465Proofs.RamRational
import Mathlib.Data.NNRat.Defs

namespace Lax455465Proofs.RamBooleanArithmetic

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational
open scoped NNRat

def bit (b : Bool) : ℚ≥0 := if b then 1 else 0

def flag (mode : Option Bool) (a b : Bool) : Bool := match mode with
  | none => a && b
  | some true => a && !b
  | some false => !a && b

def command (mode : Option Bool) : Com := .seq (.assign "rat.s" (.lit 0))
  (.seq (.assign "rat.n" (match mode with
    | none => .mul (.var "left.n") (.var "right.n")
    | some true => .mul (.var "left.n") (.sub (.lit 1) (.var "right.n"))
    | some false => .mul (.sub (.lit 1) (.var "left.n")) (.var "right.n")))
    (.assign "rat.d" (.lit 1)))

/-- Exact zero/one arithmetic for active arcs and both cut orientations. -/
theorem command_spec (B : ℕ) (mode : Option Bool) (a b : Bool) (h1 : 1 < B) :
    Spec B (fractionInputs 0 (bit a).num 1 0 (bit b).num 1) (command mode)
      (fun _ τ => FractionOutput (bit (flag mode a b) : ℚ) τ) 10 := by
  cases mode with
  | none =>
    cases a <;> cases b <;> rintro σ ⟨hs,hn,hd,hts,htn,htd⟩ <;> run_vcg
    all_goals simp_all [bit,flag,FractionOutput,fractionValue] <;> omega
  | some mode =>
    cases mode <;> cases a <;> cases b <;> rintro σ ⟨hs,hn,hd,hts,htn,htd⟩ <;> run_vcg
    all_goals simp_all [bit,flag,FractionOutput,fractionValue] <;> omega

end Lax455465Proofs.RamBooleanArithmetic
