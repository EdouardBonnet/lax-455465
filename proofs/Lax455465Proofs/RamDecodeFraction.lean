import Lax455465Proofs.RamRational
import Lax455465Proofs.RamVirtualState
import Lax455465Proofs.WordSize
import Lax455465Proofs.RamFrames

namespace Lax455465Proofs.RamDecodeFraction

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamVirtualState

/-- Normalize an unsigned input pair, with the public parser's convention
that a zero denominator denotes zero. -/
def normalize : Com := .seq (.assign "rat.s" (.lit 0))
  (.ite (.eq (.var "rat.d") (.lit 0))
    (.seq (.assign "rat.n" (.lit 0)) (.assign "rat.d" (.lit 1))) RamArithmetic.normalizeFraction)

theorem normalize_spec (B n d : ℕ) (h1 : 1 < B) (hn : n < B) (hd : d < B) :
    Spec B (fun σ => σ.vars "rat.n" = n ∧ σ.vars "rat.d" = d) normalize
      (fun _ τ => FractionOutput (NNRat.divNat n d : ℚ) τ) (36 * d.size + 22) := by
  by_cases hz : d = 0
  · subst d
    have hzero : Spec B (fun _ => True)
        (.seq (.assign "rat.n" (.lit 0)) (.assign "rat.d" (.lit 1)))
        (fun _ τ => τ.vars "rat.n" = 0 ∧ τ.vars "rat.d" = 1) 4 := by
      run_vcg
      all_goals simp
    rintro σ ⟨hnum, hden⟩
    let ν := σ.setVar "rat.s" 0
    have hfirst : Run B (.assign "rat.s" (.lit 0)) σ ν 2 := Run.assign (evalB_lit (by omega))
    obtain ⟨τ, hrun, hnτ, hdτ⟩ := hzero ν True.intro
    have hsτ : τ.vars "rat.s" = 0 := (hrun.frame_var "rat.s" (by decide)).trans (by simp [ν])
    have hcond : (Cond.eq (.var "rat.d") (.lit 0)).evalB B ν = some true := by
      rw [evalB_condEq_iff]
      exact ⟨0, 0, by rw [evalB_var_iff]; simp [ν, hden]; omega, evalB_lit (by omega), by decide⟩
    refine ⟨τ, (hfirst.seq (Run.ite_true hcond hrun)).mono (by simp [Cond.size, Expr.size]), ?_⟩
    simp [FractionOutput, fractionValue, hnτ, hdτ, hsτ]

  · have hnorm := normalizeFraction_output_spec B 0 n d (by omega) hn hd (Nat.pos_of_ne_zero hz)
    have hvalue : fractionValue 0 n d = (NNRat.divNat n d : ℚ) := by simp [fractionValue]
    rintro σ ⟨hnum, hden⟩
    run_vcg [hnorm]
    all_goals simp_all

def pair : Com := .seq (.assign "rat.n" (.get "input.data" (.var "decode.cursor")))
  (.seq (.assign "rat.d" (.get "input.data" (.add (.var "decode.cursor") (.lit 1))))
    (.seq normalize (.assign "decode.cursor" (.add (.var "decode.cursor") (.lit 2)))))

/-- Read the next input pair from the copied logical word, reduce it
exactly, and advance by precisely two input entries. -/
theorem pair_spec (B : ℕ) (words : List ℕ) (i : ℕ) (h2 : 2 < B)
    (hi : i + 1 < words.length) (hindex : i + 2 < B) (hwords : ∀ x ∈ words, x < B) :
    Spec B (fun σ => Prefix words "input.data" σ ∧ σ.vars "decode.cursor" = i) pair
      (fun _ τ => Prefix words "input.data" τ ∧ τ.vars "decode.cursor" = i + 2 ∧
        FractionOutput (NNRat.divNat words[i] words[i + 1] : ℚ) τ)
      (36 * words[i + 1].size + 34) := by
  have hi0 : i < words.length := by omega
  have hn := hwords words[i] (List.getElem_mem hi0)
  have hd := hwords words[i + 1] (List.getElem_mem hi)
  have hnorm := RamFrames.keep_scalar (normalize_spec B words[i] words[i + 1] (by omega) hn hd)
    "decode.cursor" i (by simp [normalize, RamArithmetic.normalizeFraction, RamArithmetic.gcdLoop,
      RamArithmetic.gcdDoubleStep, RamArithmetic.gcdStep, Com.wvars])
  rintro σ ⟨hp, hcursor⟩
  have hgetN := hp i hi0
  have hgetD := hp (i + 1) hi
  have harray : i + 1 < (σ.arrs "input.data").length := by
    by_contra hn
    rw [List.getElem?_eq_none (by omega)] at hgetD
    cases hgetD
  have hfinish : Spec B (fun τ => FractionOutput (NNRat.divNat words[i] words[i + 1] : ℚ) τ ∧
      τ.vars "decode.cursor" = i) (.assign "decode.cursor" (.add (.var "decode.cursor") (.lit 2)))
      (fun _ τ => τ.vars "decode.cursor" = i + 2 ∧
        FractionOutput (NNRat.divNat words[i] words[i + 1] : ℚ) τ) 4 := by
    rintro τ ⟨hf, hc⟩
    have he : (Expr.add (.var "decode.cursor") (.lit 2)).evalB B τ = some (i + 2) := by
      apply evalB_bin (op := .add) _ (evalB_lit h2) hindex
      rw [evalB_var_iff]
      exact ⟨hc.symm, hc ▸ (by omega : i < B)⟩
    exact ⟨τ.setVar "decode.cursor" (i + 2), Run.assign he, by simp,
      by simpa only [FractionOutput, vars_setVar, String.reduceEq, if_false] using hf⟩

  obtain ⟨τ, hrun, hpost⟩ : ∃ τ, Run B pair σ τ (36 * words[i + 1].size + 34) ∧
      τ.vars "decode.cursor" = i + 2 ∧ FractionOutput (NNRat.divNat words[i] words[i + 1] : ℚ) τ := by
    run_vcg [hnorm, hfinish]
    all_goals simp_all
  have harr := hrun.frame_arr "input.data" (by simp [pair, normalize,
    RamArithmetic.normalizeFraction, RamArithmetic.gcdLoop, RamArithmetic.gcdDoubleStep,
    RamArithmetic.gcdStep, Com.warrs])
  exact ⟨τ, hrun, by simpa only [Prefix, harr] using hp, hpost⟩

end Lax455465Proofs.RamDecodeFraction
