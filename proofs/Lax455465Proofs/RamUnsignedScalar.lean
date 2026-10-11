import Lax455465Proofs.RamUnsignedArithmetic

namespace Lax455465Proofs.RamUnsignedScalar

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational
open scoped NNRat

/-- Canonical unsigned rational saved in a named pair of native registers. -/
def Stored (name : String) (q : ℚ≥0) (σ : Env) : Prop :=
  σ.vars (name ++ ".n") = q.num ∧ σ.vars (name ++ ".d") = q.den

def load (name : String) : Com := .seq (.assign "rat.s" (.lit 0))
  (.seq (.assign "rat.n" (.var (name ++ ".n"))) (.assign "rat.d" (.var (name ++ ".d"))))
def save (name : String) : Com := .seq (.assign (name ++ ".n") (.var "rat.n"))
  (.assign (name ++ ".d") (.var "rat.d"))

theorem load_spec (B : ℕ) (name : String) (q : ℚ≥0) (h1 : 1 < B)
    (hn : q.num < B) (hd : q.den < B)
    (hfresh : name ++ ".n" ≠ "rat.s" ∧ name ++ ".d" ≠ "rat.s" ∧ name ++ ".d" ≠ "rat.n") :
    Spec B (Stored name q) (load name) (fun _ τ => FractionOutput (q : ℚ) τ) 6 := by
  rintro σ ⟨hnσ,hdσ⟩
  have hv := RamUnsignedArithmetic.value q
  have hns := Ne.symm hfresh.1
  have hds := Ne.symm hfresh.2.1
  have hdn := Ne.symm hfresh.2.2
  run_vcg
  all_goals simp_all [FractionOutput,NNRat.natAbs_num_coe,NNRat.den_coe]

theorem save_spec (B : ℕ) (name : String) (q : ℚ≥0)
    (hn : q.num < B) (hd : q.den < B) (hfresh : name ++ ".n" ≠ "rat.d") :
    Spec B (FractionOutput (q : ℚ)) (save name) (fun _ τ => Stored name q τ) 4 := by
  rintro σ ⟨hv,hnσ,hdσ,hs⟩
  have hn' : σ.vars "rat.n" = q.num := by simpa only [NNRat.natAbs_num_coe] using hnσ
  have hd' : σ.vars "rat.d" = q.den := by simpa only [NNRat.den_coe] using hdσ
  have hdn := Ne.symm hfresh
  run_vcg
  all_goals simp_all [Stored]

end Lax455465Proofs.RamUnsignedScalar
