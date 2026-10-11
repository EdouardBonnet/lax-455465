import Lax455465Proofs.RamRational
import Lax455465Proofs.RamWordBuffer
import Lax109476.RationalEncoding

namespace Lax455465Proofs.RamFractionEncoding

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamVirtualState

/-- A zero numerator always emits the canonical nonnegative sign, even
when an arithmetic operation kept a negative sign for its zero value. -/
theorem canonical_sign (q : ℚ) (σ : Env) (h : FractionOutput q σ) :
    (if σ.vars "rat.n" = 0 then 0 else σ.vars "rat.s") = if q.num < 0 then 1 else 0 := by
  by_cases hn : σ.vars "rat.n" = 0
  · have hnum : q.num = 0 := by
      have he : q.num.natAbs = 0 := h.2.1.symm.trans hn
      exact Int.natAbs_eq_zero.mp he
    simp [hn, hnum]
  · have hs : σ.vars "rat.s" = 0 ∨ σ.vars "rat.s" = 1 := by have := h.2.2.2; omega
    rcases hs with hs | hs
    · have hnonneg : 0 ≤ q := by
        rw [← h.1]
        simp only [fractionValue, hs, show ¬(0 : ℕ) = 1 by decide, if_false]
        positivity
      have hnum := Rat.num_nonneg.mpr hnonneg
      simp [hn, hs, not_lt.mpr hnum]
    · have hnpos : (0 : ℚ) < σ.vars "rat.n" := by exact_mod_cast (show 0 < σ.vars "rat.n" by omega)
      have hdpos : (0 : ℚ) < σ.vars "rat.d" := by
        rw [h.2.2.1]
        exact_mod_cast q.den_pos
      have hneg : q < 0 := by
        rw [← h.1]
        simp only [fractionValue, hs, if_true]
        exact div_neg_of_neg_of_pos (by linarith) hdpos
      have hnum : q.num < 0 := by
        by_contra hnum
        have hq := Rat.num_nonneg.mp (show 0 ≤ q.num by omega)
        linarith
      simp [hn, hs, hnum]

def sign : Com := .ite (.eq (.var "rat.n") (.lit 0))
  (.assign "emit.s" (.lit 0)) (.assign "emit.s" (.var "rat.s"))

theorem sign_spec (B : ℕ) (q : ℚ) (h1 : 1 < B) (hn : q.num.natAbs < B) :
    Spec B (FractionOutput q) sign
      (fun _ τ => τ.vars "emit.s" = if q.num < 0 then 1 else 0) 6 := by
  intro σ h
  have hvalue := h.2.1
  have hsign := h.2.2.2
  have hcanonical := canonical_sign q σ h
  run_vcg
  all_goals simp_all

def emit : Com := .seq sign (.seq (RamWordBuffer.append "lp.word" "lp.position" (.var "emit.s"))
  (.seq (RamWordBuffer.append "lp.word" "lp.position" (.var "rat.n"))
    (RamWordBuffer.append "lp.word" "lp.position" (.var "rat.d"))))

/-- Emit precisely the public LP rational encoding into its native buffer,
including the canonical sign of zero. Each initialized word is preserved. -/
theorem emit_spec (B : ℕ) (q : ℚ) (words : List ℕ) (h1 : 1 < B)
    (hn : q.num.natAbs < B) (hd : q.den < B) (hlen : words.length + 3 < B) :
    Spec B (fun σ => FractionOutput q σ ∧ Prefix words "lp.word" σ ∧
      σ.vars "lp.position" = words.length ∧ words.length + 2 < (σ.arrs "lp.word").length) emit
      (fun _ τ => Prefix (words ++ Lax109476.RationalEncoding.encodeRational q) "lp.word" τ ∧
        τ.vars "lp.position" = words.length + 3) 27 := by
  rintro σ ⟨hf, hp, hpos, hroom⟩
  let tag := if q.num < 0 then 1 else 0
  have htag : tag < B := by dsimp only [tag]; split_ifs <;> omega
  obtain ⟨ν, hsign, htagν⟩ := sign_spec B q h1 hn σ hf
  have hnumν := (hsign.frame_var "rat.n" (by simp [sign, Com.wvars])).trans hf.2.1
  have hdenν := (hsign.frame_var "rat.d" (by simp [sign, Com.wvars])).trans hf.2.2.1
  have hposν := (hsign.frame_var "lp.position" (by simp [sign, Com.wvars])).trans hpos
  have hpν : Prefix words "lp.word" ν := by
    simpa only [Prefix, hsign.frame_arr "lp.word" (by simp [sign, Com.warrs])] using hp
  have hroomν : words.length + 2 < (ν.arrs "lp.word").length := by
    rwa [RamFrames.run_array_length hsign "lp.word"]
  have hnum := RamFrames.keep_scalar (RamFrames.keep_scalar
    (RamWordBuffer.append_spec B "lp.word" "lp.position" words tag (.var "emit.s") h1 (by omega))
    "rat.n" q.num.natAbs (by simp [RamWordBuffer.append, Com.wvars]))
    "rat.d" q.den (by simp [RamWordBuffer.append, Com.wvars])
  obtain ⟨μ, hfirst, hfirstPost⟩ := hnum ν ⟨⟨⟨hpν, hposν, by omega,
    by rw [evalB_var_iff]; exact ⟨htagν.symm, htagν ▸ htag⟩⟩, hnumν⟩, hdenν⟩
  have hroomμ : (words ++ [tag]).length + 1 < (μ.arrs "lp.word").length := by
    rw [RamFrames.run_array_length hfirst "lp.word", List.length_append, List.length_singleton]
    exact hroomν
  have hden := RamFrames.keep_scalar
    (RamWordBuffer.append_spec B "lp.word" "lp.position" (words ++ [tag]) q.num.natAbs (.var "rat.n") h1
      (by simp only [List.length_append, List.length_singleton]; omega))
    "rat.d" q.den (by simp [RamWordBuffer.append, Com.wvars])
  obtain ⟨ρ, hsecond, hsecondPost⟩ := hden μ ⟨⟨hfirstPost.1.1.1,
    by simpa only [List.length_append, List.length_singleton] using hfirstPost.1.1.2,
    by omega, by rw [evalB_var_iff]; exact ⟨hfirstPost.1.2.symm, hfirstPost.1.2 ▸ hn⟩⟩, hfirstPost.2⟩
  have hroomρ : ((words ++ [tag]) ++ [q.num.natAbs]).length < (ρ.arrs "lp.word").length := by
    rw [RamFrames.run_array_length hsecond "lp.word", List.length_append, List.length_singleton]
    exact hroomμ
  obtain ⟨τ, hthird, hthirdPost⟩ := RamWordBuffer.append_spec B "lp.word" "lp.position"
    ((words ++ [tag]) ++ [q.num.natAbs]) q.den (.var "rat.d") h1
    (by simp only [List.length_append, List.length_singleton]; omega) ρ
    ⟨hsecondPost.1.1, by simpa only [List.length_append, List.length_singleton] using hsecondPost.1.2,
      hroomρ, by rw [evalB_var_iff]; exact ⟨hsecondPost.2.symm, hsecondPost.2 ▸ hd⟩⟩
  refine ⟨τ, (hsign.seq (hfirst.seq (hsecond.seq hthird))).mono (by simp [Expr.size]), ?_⟩
  simpa only [Lax109476.RationalEncoding.encodeRational, tag, List.append_assoc,
    List.cons_append, List.nil_append, List.length_append, List.length_singleton, List.length_cons, List.length_nil, Nat.add_assoc]
    using hthirdPost

end Lax455465Proofs.RamFractionEncoding
