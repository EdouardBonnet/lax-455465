import Lax455465Proofs.RegisteredLpNative
import Lax455465Proofs.RamLpPrepare

namespace Lax455465Proofs.RegisteredLpInvocation

open Lax109476.LinearProgram Lax109476.RationalCertificates Lax109476.RationalEncoding
open Lax759944.BinaryWordEncoding Lax759944.RamPolytime
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState

/-- One fixed native invocation computes its virtual word width from the
actual LP encoding, supplies its exact physical input, and executes the
registered black-box solver into a private certificate buffer. -/
def command (p : Lax808846.Ram.Program) (coefficients : List ℕ) : Com :=
  .seq (RamLpPrepare.command coefficients) (RamVirtualProgram.execute p)

theorem exists_program :
    ∃ (p : Lax808846.Ram.Program) (wordBound timeBound : Polynomial ℕ) (coefficients : List ℕ),
      (∀ x : ℕ, RamPolynomial.value coefficients x = wordBound.eval x) ∧
      ∀ (m n : ℕ) (P : Program ℚ m n), ∃ certificate : Certificate m n,
        IsValidCertificate P certificate ∧
        FitsInWords (wordBound.eval (bitSize (encodeProgram P)))
          (((encodeProgram P).length :: encodeProgram P) ++ encodeCertificate certificate) ∧
        ∀ B : ℕ,
          bitSize (encodeProgram P) + 1 < B →
          wordBound.eval (bitSize (encodeProgram P) + 1) < B →
          2 * (2 ^ wordBound.eval (bitSize (encodeProgram P))) ^ 2 + 3 < B →
          timeBound.eval (bitSize (encodeProgram P)) + 1 < B →
          RamVirtualConstants.allowance p < B →
          Spec B (fun σ => Prefix (encodeProgram P) "lp.word" σ ∧
            σ.vars "lp.position" = (encodeProgram P).length ∧
            (encodeProgram P).length < (σ.arrs "vm.input").length ∧
            timeBound.eval (bitSize (encodeProgram P)) < (σ.arrs "vm.addresses").length ∧
            timeBound.eval (bitSize (encodeProgram P)) < (σ.arrs "vm.values").length ∧
            timeBound.eval (bitSize (encodeProgram P)) < (σ.arrs "vm.output").length)
            (command p coefficients)
            (fun _ τ => Prefix (encodeCertificate certificate) "vm.output" τ ∧
              τ.vars "vm.outputLength" = (encodeCertificate certificate).length ∧
              τ.vars "vm.running" = 0)
            (((12 * bitSize (encodeProgram P) + 39) * (encodeProgram P).length +
                6 * coefficients.length + 29) +
              ((timeBound.eval (bitSize (encodeProgram P)) + 1) *
                (4 * p.length + 32 * timeBound.eval (bitSize (encodeProgram P)) + 104) + 18)) := by
  obtain ⟨p, wordBound, timeBound, hnative⟩ := RegisteredLpNative.exists_program
  obtain ⟨coefficients, hcoeff⟩ := RamPolynomial.exists_coefficients wordBound
  refine ⟨p, wordBound, timeBound, coefficients, hcoeff, ?_⟩
  intro m n P
  obtain ⟨certificate, hvalid, hfit, hrun⟩ := hnative m n P
  refine ⟨certificate, hvalid, hfit, ?_⟩
  intro B hsize hpoly hB htime hallow
  let w := wordBound.eval (bitSize (encodeProgram P))
  let T := timeBound.eval (bitSize (encodeProgram P))
  have hM : 2 ^ w < B := by nlinarith [Nat.two_pow_pos w]
  have hlenWord : (encodeProgram P).length < 2 ^ w :=
    hfit _ (List.mem_append_left _ List.mem_cons_self)
  have hlen : (encodeProgram P).length + 1 < B := by omega
  have hwords : ∀ x ∈ encodeProgram P, x < B := fun x hx =>
    (hfit x (List.mem_append_left _ (List.mem_cons_of_mem _ hx))).trans hM
  have hprepare := RamLpPrepare.command_spec B coefficients (encodeProgram P) (by omega)
    hlen hsize hwords (by simpa only [hcoeff] using hpoly)
  rintro σ ⟨hp, hpos, hinputRoom, hA, hV, hO⟩
  obtain ⟨ν, hprep, hprepared⟩ := hprepare σ ⟨hp, hpos, hinputRoom⟩
  have hAν : T < (ν.arrs "vm.addresses").length := by
    rwa [RamFrames.run_array_length hprep "vm.addresses"]
  have hVν : T < (ν.arrs "vm.values").length := by
    rwa [RamFrames.run_array_length hprep "vm.values"]
  have hOν : T < (ν.arrs "vm.output").length := by
    rwa [RamFrames.run_array_length hprep "vm.output"]
  obtain ⟨τ, hsolve, hpost⟩ := hrun B hB htime hallow ν
    ⟨by simpa only [hcoeff] using hprepared.1, hprepared.2.1, hprepared.2.2, hAν, hVν, hOν⟩
  exact ⟨τ, hprep.seq hsolve, hpost⟩

end Lax455465Proofs.RegisteredLpInvocation
