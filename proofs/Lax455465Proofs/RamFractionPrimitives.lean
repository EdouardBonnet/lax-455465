import Lax455465Proofs.RamRational

namespace Lax455465Proofs.RamFractionPrimitives

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational

def zero : Com := .seq (.assign "rat.s" (.lit 0))
  (.seq (.assign "rat.n" (.lit 0)) (.assign "rat.d" (.lit 1)))
def one : Com := .seq (.assign "rat.s" (.lit 0))
  (.seq (.assign "rat.n" (.lit 1)) (.assign "rat.d" (.lit 1)))
def negativeOne : Com := .seq (.assign "rat.s" (.lit 1))
  (.seq (.assign "rat.n" (.lit 1)) (.assign "rat.d" (.lit 1)))
def negate : Com := .assign "rat.s" (.sub (.lit 1) (.var "rat.s"))

theorem zero_spec (B : ℕ) (h1 : 1 < B) :
    Spec B (fun _ => True) zero (fun _ τ => FractionOutput 0 τ) 6 := by
  run_vcg
  all_goals simp [FractionOutput,fractionValue]

theorem one_spec (B : ℕ) (h1 : 1 < B) :
    Spec B (fun _ => True) one (fun _ τ => FractionOutput 1 τ) 6 := by
  run_vcg
  all_goals simp [FractionOutput,fractionValue]

theorem negativeOne_spec (B : ℕ) (h1 : 1 < B) :
    Spec B (fun _ => True) negativeOne (fun _ τ => FractionOutput (-1) τ) 6 := by
  run_vcg
  all_goals simp [FractionOutput,fractionValue]

theorem negate_spec (B : ℕ) (q : ℚ) (h1 : 1 < B) :
    Spec B (FractionOutput q) negate (fun _ τ => FractionOutput (-q) τ) 4 := by
  rintro σ ⟨hvalue,hn,hd,hs⟩
  have hsign : σ.vars "rat.s" = 0 ∨ σ.vars "rat.s" = 1 := by omega
  rcases hsign with hs₀ | hs₁
  · run_vcg
    all_goals simp_all [FractionOutput,fractionValue,Rat.neg_num,Int.natAbs_neg,Rat.neg_den,neg_div]
  · run_vcg
    all_goals simp_all [FractionOutput,fractionValue,Rat.neg_num,Int.natAbs_neg,Rat.neg_den,neg_div]
    all_goals linarith

end Lax455465Proofs.RamFractionPrimitives
