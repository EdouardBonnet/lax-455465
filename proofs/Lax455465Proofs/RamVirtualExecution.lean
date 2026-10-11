import Lax455465Proofs.RamVirtualLoop

namespace Lax455465Proofs.RamVirtualExecution

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamVirtualCore RamVirtualProgram RamVirtualState RamVirtualInstruction

/-- Initializing and executing the fixed native interpreter reproduces a
complete source run from the registered zero-memory initial state. Its
arrays may contain stale entries: their logical prefixes start empty. -/
theorem execute_spec (B w k : ℕ) (p : Lax808846.Ram.Program) (input : List ℕ)
    (f : SparseRam.SparseState) (hB : 2 * (2 ^ w) ^ 2 + 3 < B)
    (hk : k + 1 < B) (hp : p.length + 1 < B)
    (hlit : ∀ i ∈ p, LiteralsFit (B - 1) i)
    (hinput : input.length < B) (hinputWords : ∀ x ∈ input, x < B)
    (hr : SparseRam.run w p k (SparseRam.init input) = some f)
    (hhalt : SparseRam.step w p f = none) :
    Spec B (fun σ => σ.vars "vm.width" = w ∧ Prefix input "vm.input" σ ∧
      σ.vars "vm.inputLength" = input.length ∧ k < (σ.arrs "vm.addresses").length ∧
      k < (σ.arrs "vm.values").length ∧ k < (σ.arrs "vm.output").length)
      (execute p) (fun _ τ => Represents w f τ ∧ τ.vars "vm.running" = 0)
      ((k + 1) * (4 * p.length + 32 * k + 104) + 18) := by
  have h1 : 1 < B := by omega
  have hM : 2 ^ w < B := by nlinarith [Nat.two_pow_pos w]
  rintro σ ⟨hwidth, hprefix, hlen, hA, hV, hO⟩
  obtain ⟨ν, hmod, hmodulus⟩ := RamWordOps.modulus_spec B w hM σ hwidth
  have hwidthν := (hmod.frame_var "vm.width" (by decide)).trans hwidth
  have hprefixν : Prefix input "vm.input" ν := by
    simpa only [Prefix, hmod.frame_arr "vm.input" (by decide)] using hprefix
  have hlenν := (hmod.frame_var "vm.inputLength" (by decide)).trans hlen
  obtain ⟨μ, hinit, hrep⟩ := init_spec B w input h1 ν ⟨hmodulus, hwidthν, hprefixν, hlenν⟩
  have hAμ : k < (μ.arrs "vm.addresses").length := by
    rwa [RamFrames.run_array_length hinit "vm.addresses", RamFrames.run_array_length hmod "vm.addresses"]
  have hVμ : k < (μ.arrs "vm.values").length := by
    rwa [RamFrames.run_array_length hinit "vm.values", RamFrames.run_array_length hmod "vm.values"]
  have hOμ : k < (μ.arrs "vm.output").length := by
    rwa [RamFrames.run_array_length hinit "vm.output", RamFrames.run_array_length hmod "vm.output"]
  have hpcs : ∀ j ≤ k, ∀ t, SparseRam.run w p j (SparseRam.init input) = some t → t.pc + 1 < B := by
    intro j _ t hj
    exact RamVirtualTraceBounds.run_pc B w p (SparseRam.init input) t j hp hlit (by simp [SparseRam.init]; omega) hj
  have hwords : SparseBounds.MemoryWords w (SparseRam.init input).memory := by
    simp [SparseBounds.MemoryWords, SparseRam.init]
  obtain ⟨τ, hloop, hfinal⟩ := RamVirtualLoop.loop_spec B w k k p (SparseRam.init input) f hB hk
    (by omega) (fun i hi => RamVirtualTraceBounds.literals_mono i (hlit i hi) (by omega))
    hwords hinput hinputWords (by simp [SparseRam.init]) (by simp [SparseRam.init]) hpcs hr hhalt μ
    ⟨hrep.1, hrep.2, hAμ, hVμ, hOμ⟩
  exact ⟨τ, (hmod.seq (hinit.seq hloop)).mono (by omega), hfinal⟩

end Lax455465Proofs.RamVirtualExecution
