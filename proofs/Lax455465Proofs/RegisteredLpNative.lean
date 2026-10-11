import Lax455465Proofs.RegisteredLpExecution
import Lax455465Proofs.RamVirtualExecution
import Lax455465Proofs.RamVirtualConstants

namespace Lax455465Proofs.RegisteredLpNative

open Lax109476.LinearProgram Lax109476.RationalCertificates Lax109476.RationalEncoding
open Lax759944.BinaryWordEncoding Lax759944.RamPolytime
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamVirtualState RamVirtualProgram

/-- The registered concept theorem gives one fixed LP program. Its native
invocation produces the exact valid certificate in a private buffer, with
quadratic simulation overhead and no LP implementation-package import. -/
theorem exists_program :
    ∃ (p : Lax808846.Ram.Program) (wordBound timeBound : Polynomial ℕ),
      ∀ (m n : ℕ) (P : Program ℚ m n), ∃ certificate : Certificate m n,
        IsValidCertificate P certificate ∧
        FitsInWords (wordBound.eval (bitSize (encodeProgram P)))
          (((encodeProgram P).length :: encodeProgram P) ++ encodeCertificate certificate) ∧
        ∀ B : ℕ,
          2 * (2 ^ wordBound.eval (bitSize (encodeProgram P))) ^ 2 + 3 < B →
          timeBound.eval (bitSize (encodeProgram P)) + 1 < B →
          RamVirtualConstants.allowance p < B →
          Spec B (fun σ => σ.vars "vm.width" = wordBound.eval (bitSize (encodeProgram P)) ∧
            Prefix ((encodeProgram P).length :: encodeProgram P) "vm.input" σ ∧
            σ.vars "vm.inputLength" = (encodeProgram P).length + 1 ∧
            timeBound.eval (bitSize (encodeProgram P)) < (σ.arrs "vm.addresses").length ∧
            timeBound.eval (bitSize (encodeProgram P)) < (σ.arrs "vm.values").length ∧
            timeBound.eval (bitSize (encodeProgram P)) < (σ.arrs "vm.output").length)
            (execute p)
            (fun _ τ => Prefix (encodeCertificate certificate) "vm.output" τ ∧
              τ.vars "vm.outputLength" = (encodeCertificate certificate).length ∧
              τ.vars "vm.running" = 0)
            ((timeBound.eval (bitSize (encodeProgram P)) + 1) *
              (4 * p.length + 32 * timeBound.eval (bitSize (encodeProgram P)) + 104) + 18) := by
  obtain ⟨p, wordBound, timeBound, hprogram⟩ := RegisteredLpExecution.exists_program
  refine ⟨p, wordBound, timeBound, ?_⟩
  intro m n P
  obtain ⟨certificate, hvalid, hfit, k, hk, s, hrun, hhalt, hout, _⟩ := hprogram m n P
  refine ⟨certificate, hvalid, hfit, ?_⟩
  intro B hB htime hallow
  let w := wordBound.eval (bitSize (encodeProgram P))
  let T := timeBound.eval (bitSize (encodeProgram P))
  let input := (encodeProgram P).length :: encodeProgram P
  have hM : 2 ^ w < B := by nlinarith [Nat.two_pow_pos w]
  have hinput : FitsInWords w input := fun x hx => hfit x (List.mem_append_left _ hx)
  have hlenWord : (encodeProgram P).length < 2 ^ w := hinput _ List.mem_cons_self
  have hlen : input.length < B := by simp only [input, List.length_cons]; omega
  have hwords : ∀ x ∈ input, x < B := fun x hx => (hinput x hx).trans hM
  have hp : p.length + 1 < B := (RamVirtualConstants.length_bound p).trans hallow
  have hlit : ∀ i ∈ p, RamVirtualInstruction.LiteralsFit (B - 1) i := fun i hi =>
    RamVirtualTraceBounds.literals_mono i (RamVirtualConstants.literals_fit p i hi) (by omega)
  have hnative := RamVirtualExecution.execute_spec B w k p input s hB (by omega) hp hlit
    hlen hwords hrun hhalt
  apply ((hnative.pre ?_).post ?_).mono ?_
  · rintro σ ⟨hwidth, hprefix, hinputlen, hA, hV, hO⟩
    exact ⟨hwidth, hprefix, hinputlen, by omega, by omega, by omega⟩
  · rintro σ τ _ ⟨hrep, hflag⟩
    have htapes := hrep.2
    exact ⟨by simpa only [hout] using htapes.2.2.2.2.1,
      by simpa only [hout] using htapes.2.2.2.2.2, hflag⟩
  · have hprod := Nat.mul_le_mul (Nat.add_le_add_right hk 1)
      (show 4 * p.length + 32 * k + 104 ≤ 4 * p.length + 32 * T + 104 by omega)
    dsimp only [T] at hprod
    omega

end Lax455465Proofs.RegisteredLpNative
