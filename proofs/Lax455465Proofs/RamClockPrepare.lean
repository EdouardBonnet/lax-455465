import Lax455465Proofs.RamBitSize
import Lax455465Proofs.RamPolynomial
import Lax455465Proofs.RamLpInputFrame

namespace Lax455465Proofs.RamClockPrepare

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState
open Lax759944.BinaryWordEncoding

/-- The virtual width is computed from the copied input's actual binary size.
The host's word width is never queried or used as the virtual width. -/
def command (coefficients : List ℕ) : Com := .seq (RamBitSize.array "lp.word" "lp.position")
  (.seq (.assign "poly.argument" (.var "size.total"))
    (.seq (RamPolynomial.command coefficients)
      (.seq (.assign "vm.width" (.var "poly.value")) RamLpInputFrame.command)))

theorem command_spec (B : ℕ) (coefficients : List ℕ) (xs : List ℕ) (h2 : 2 < B)
    (hlen : xs.length + 1 < B) (hsize : bitSize xs + 1 < B) (hwords : ∀ x ∈ xs, x < B)
    (hvalue : RamPolynomial.value coefficients (bitSize xs + 1) < B) :
    Spec B (fun σ => Prefix xs "lp.word" σ ∧ σ.vars "lp.position" = xs.length ∧
      xs.length < (σ.arrs "vm.input").length) (command coefficients)
      (fun _ τ => (τ.vars "vm.width" = RamPolynomial.value coefficients (bitSize xs) ∧
        Prefix (xs.length :: xs) "vm.input" τ ∧ τ.vars "vm.inputLength" = xs.length + 1) ∧
        τ.vars "poly.argument"=bitSize xs)
      ((12 * bitSize xs + 39) * xs.length + 6 * coefficients.length + 29) := by
  rintro σ ⟨hp, hpos, hroom⟩
  obtain ⟨ν, hcount, htotal⟩ := RamBitSize.array_spec B xs "lp.word" "lp.position"
    (by decide) h2 (by omega) hsize hwords σ ⟨hpos, hp⟩
  let δ := ν.setVar "poly.argument" (bitSize xs)
  have harg : Run B (.assign "poly.argument" (.var "size.total")) ν δ 2 :=
    Run.assign (by rw [evalB_var_iff]; exact ⟨htotal.symm, htotal ▸ (by omega : bitSize xs < B)⟩)
  obtain ⟨μ, hpoly, hpolyValue⟩ := RamPolynomial.command_spec B coefficients (bitSize xs)
    (by omega) (by omega) hvalue δ (by simp [δ])
  have hv : RamPolynomial.value coefficients (bitSize xs) < B :=
    (RamPolynomial.value_mono coefficients (show bitSize xs ≤ bitSize xs + 1 by omega)).trans_lt hvalue
  let ε := μ.setVar "vm.width" (RamPolynomial.value coefficients (bitSize xs))
  have hwidth : Run B (.assign "vm.width" (.var "poly.value")) μ ε 2 :=
    Run.assign (by rw [evalB_var_iff]; exact ⟨hpolyValue.symm, hpolyValue ▸ hv⟩)
  have hpν : Prefix xs "lp.word" ν := by
    simpa only [Prefix, hcount.frame_arr "lp.word" (by simp [RamBitSize.array,
      RamBitSize.arrayStep, RamBitSize.word, RamBitSize.wordLoop, RamBitSize.wordStep, Com.warrs])] using hp
  have hposν := (hcount.frame_var "lp.position" (by simp [RamBitSize.array, RamBitSize.arrayStep,
    RamBitSize.word, RamBitSize.wordLoop, RamBitSize.wordStep, Com.wvars])).trans hpos
  have hpμ : Prefix xs "lp.word" μ := by
    simpa only [Prefix, hpoly.frame_arr "lp.word" (by simp [RamPolynomial.arrays_frame]), δ, arrs_setVar] using hpν
  have hposμ := (hpoly.frame_var "lp.position" (RamPolynomial.variable_frame coefficients _ (by decide))).trans
    (show δ.vars "lp.position" = xs.length by simpa [δ] using hposν)
  have hpε : Prefix xs "lp.word" ε := by simpa only [Prefix, ε, arrs_setVar] using hpμ
  have hposε : ε.vars "lp.position" = xs.length := by simpa [ε] using hposμ
  have hroomε : xs.length < (ε.arrs "vm.input").length := by
    rw [show ε.arrs "vm.input" = μ.arrs "vm.input" from rfl,
      RamFrames.run_array_length hpoly "vm.input", show δ.arrs "vm.input" = ν.arrs "vm.input" from rfl,
      RamFrames.run_array_length hcount "vm.input"]
    exact hroom
  obtain ⟨τ, hframe, hpost⟩ := RamLpInputFrame.command_spec B xs (by omega) hlen hwords ε ⟨hpε, hposε, hroomε⟩
  have hwτ : τ.vars "vm.width" = RamPolynomial.value coefficients (bitSize xs) :=
    (hframe.frame_var "vm.width" (by simp [RamLpInputFrame.command, RamLpInputFrame.step,
      RamWordBuffer.append, Com.wvars])).trans (by simp [ε])
  have hargμ : μ.vars "poly.argument"=bitSize xs :=
    (hpoly.frame_var _ (RamPolynomial.argument_frame coefficients)).trans (by simp [δ])
  have hargτ : τ.vars "poly.argument"=bitSize xs :=
    (hframe.frame_var _ (by decide)).trans (by simpa [ε] using hargμ)
  refine ⟨τ, (hcount.seq (harg.seq (hpoly.seq (hwidth.seq hframe)))).mono ?_, ⟨hwτ, hpost⟩,hargτ⟩
  nlinarith


def boundedCommand (widthCoefficients timeCoefficients : List ℕ) : Com :=
  .seq (command widthCoefficients) (.seq (RamPolynomial.command timeCoefficients)
    (.assign "clock.remaining" (.var "poly.value")))

theorem bounded_spec (B : ℕ) (wc tc : List ℕ) (xs : List ℕ) (h2 : 2 < B)
    (hlen : xs.length+1 < B) (hsize : bitSize xs+1 < B) (hwords : ∀ a∈xs,a < B)
    (hw : RamPolynomial.value wc (bitSize xs+1) < B) (ht : RamPolynomial.value tc (bitSize xs+1) < B) :
    Spec B (fun σ => Prefix xs "lp.word" σ ∧ σ.vars "lp.position"=xs.length ∧
      xs.length < (σ.arrs "vm.input").length) (boundedCommand wc tc)
      (fun _ τ => τ.vars "vm.width"=RamPolynomial.value wc (bitSize xs) ∧
        Prefix (xs.length::xs) "vm.input" τ ∧ τ.vars "vm.inputLength"=xs.length+1 ∧
        τ.vars "clock.remaining"=RamPolynomial.value tc (bitSize xs))
      ((12*bitSize xs+39)*xs.length+6*wc.length+6*tc.length+33) := by
  intro σ hσ
  obtain ⟨ν,r1,p1,harg⟩ := command_spec B wc xs h2 hlen hsize hwords hw σ hσ
  obtain ⟨μ,r2,p2⟩ := RamPolynomial.command_spec B tc (bitSize xs) (by omega) (by omega) ht ν harg
  let N := RamPolynomial.value tc (bitSize xs)
  have hNB : N < B := (RamPolynomial.value_mono tc (show bitSize xs ≤ bitSize xs+1 by omega)).trans_lt ht
  let τ := μ.setVar "clock.remaining" N
  have r3 : Run B (.assign "clock.remaining" (.var "poly.value")) μ τ 2 := Run.assign (by
    rw [evalB_var_iff]; exact ⟨p2.symm,p2 ▸ hNB⟩)
  refine ⟨τ,(r1.seq (r2.seq r3)).mono (by omega),?_,?_,?_,by simp [τ,N]⟩
  · simpa only [τ,vars_setVar,String.reduceEq,if_false] using
      (r2.frame_var "vm.width" (RamPolynomial.variable_frame tc _ (by decide))).trans p1.1
  · simpa only [τ,arrs_setVar,Prefix,r2.frame_arr "vm.input" (by rw [RamPolynomial.arrays_frame]; simp)] using p1.2.1
  · simpa only [τ,vars_setVar,String.reduceEq,if_false] using
      (r2.frame_var "vm.inputLength" (RamPolynomial.variable_frame tc _ (by decide))).trans p1.2.2

end Lax455465Proofs.RamClockPrepare
