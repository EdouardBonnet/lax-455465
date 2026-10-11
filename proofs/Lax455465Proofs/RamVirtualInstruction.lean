import Lax455465Proofs.RamVirtualFrame
import Lax455465Proofs.RamVirtualBasic
import Lax455465Proofs.RamVirtualBitOps
import Lax455465Proofs.RamVirtualControl
import Lax455465Proofs.RamVirtualIndirect
import Lax455465Proofs.RamVirtualInput
import Lax455465Proofs.RamVirtualRead
import Lax455465Proofs.RamVirtualOutput

namespace Lax455465Proofs.RamVirtualInstruction

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamVirtualCore RamVirtualArithmetic RamVirtualProgram RamVirtualState RamVirtualFrame

/-- Only the finitely many literal operands of the fixed source program
need a native bound; virtual addresses themselves may span its whole word. -/
def LiteralsFit (B : ℕ) : Lax808846.Ram.Instr → Prop
  | .set a v => a < B ∧ v < B
  | .load a b | .store a b | .not a b | .inputLoad a b => a < B ∧ b < B
  | .add a b c | .sub a b c | .mul a b c | .div a b c | .and a b c | .shiftl a b c =>
      a < B ∧ b < B ∧ c < B
  | .jzero a l => a < B ∧ l < B
  | .jump l | .jeof l => l < B
  | .inputLength a | .read a | .write a => a < B
  | .halt => True

def Ready (w : ℕ) (s : SparseRam.SparseState) (σ : Env) : Prop :=
  Represents w s σ ∧ σ.vars "vm.running" = 1 ∧
  s.memory.length < (σ.arrs "vm.addresses").length ∧
  s.memory.length < (σ.arrs "vm.values").length ∧
  s.out.length < (σ.arrs "vm.output").length

def Result (w : ℕ) (s : SparseRam.SparseState) (i : Lax808846.Ram.Instr) (τ : Env) : Prop :=
  match SparseRam.effect w i s with
  | some t => Represents w t τ ∧ τ.vars "vm.running" = 1
  | none => Represents w s τ ∧ τ.vars "vm.running" = 0

/-- All eighteen native instruction commands implement the registered RAM
semantics, including exhausted reads and the explicit halt instruction. -/
theorem instruction_spec (B w : ℕ) (s : SparseRam.SparseState) (i : Lax808846.Ram.Instr)
    (hB : 2 * (2 ^ w) ^ 2 + 3 < B) (hlit : LiteralsFit B i)
    (hwords : SparseBounds.MemoryWords w s.memory)
    (hinput : s.input.length < B) (hinputWords : ∀ x ∈ s.input, x < B)
    (hpc : s.pc + 1 < B) (hmem : s.memory.length + 1 < B) (hout : s.out.length + 1 < B) :
    Spec B (Ready w s) (instruction i) (fun _ τ => Result w s i τ)
      (32 * s.memory.length + 100) := by
  have h1 : 1 < B := by omega
  have hM : 2 ^ w < B := by nlinarith [Nat.two_pow_pos w]
  have lift (j : Lax808846.Ram.Instr) (t : SparseRam.SparseState) (K : ℕ) (P : Env → Prop)
      (hq : Quiet j) (ht : t.input = s.input ∧ t.inp = s.inp ∧ t.out = s.out)
      (hspec : Spec B P (instruction j) (fun _ τ => Core w t.pc t.memory τ) K)
      (hpre : ∀ σ, Represents w s σ → s.memory.length < (σ.arrs "vm.addresses").length →
        s.memory.length < (σ.arrs "vm.values").length → P σ)
      (hK : K ≤ 32 * s.memory.length + 100) :
      Spec B (Ready w s) (instruction j)
        (fun _ τ => Represents w t τ ∧ τ.vars "vm.running" = 1) (32 * s.memory.length + 100) :=
    ((lift_spec B w K j s t P hq ht hspec hpre).pre
      (fun _ h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩)).mono hK
  cases i with
  | set a v =>
    exact lift (.set a v) (SparseRam.assign w s a v) 40 _ trivial ⟨rfl, rfl, rfl⟩
      (set_spec B w s.pc s.memory a v h1 hM hlit.1 hlit.2 hpc hmem)
      (fun _ h hA hV => ⟨h.1, hA, hV⟩) (by omega)
  | load a b =>
    exact lift (.load a b) (SparseRam.assign w s a
        (SparseRam.lookup s.memory (SparseRam.lookup s.memory (b % 2 ^ w) % 2 ^ w))) _ _
      trivial ⟨rfl, rfl, rfl⟩
      (RamVirtualIndirect.load_core_spec B w s.pc s.memory a b h1 hM hlit.1 hlit.2 hwords hpc hmem)
      (fun _ h hA hV => ⟨h.1, hA, hV⟩) (by omega)
  | store a b =>
    exact lift (.store a b) (SparseRam.assign w s (SparseRam.lookup s.memory (a % 2 ^ w))
        (SparseRam.lookup s.memory (b % 2 ^ w))) _ _ trivial ⟨rfl, rfl, rfl⟩
      (RamVirtualIndirect.store_core_spec B w s.pc s.memory a b h1 hM hlit.1 hlit.2 hwords hpc hmem)
      (fun _ h hA hV => ⟨h.1, hA, hV⟩) (by omega)
  | add a b c =>
    exact ((RamVirtualBasic.instruction_spec B w .add s a b c hB hlit.1 hlit.2.1 hlit.2.2
      hwords hpc hmem).pre (fun _ h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩)).mono (by omega)
  | sub a b c =>
    exact ((RamVirtualBasic.instruction_spec B w .sub s a b c hB hlit.1 hlit.2.1 hlit.2.2
      hwords hpc hmem).pre (fun _ h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩)).mono (by omega)
  | mul a b c =>
    exact ((RamVirtualBasic.instruction_spec B w .mul s a b c hB hlit.1 hlit.2.1 hlit.2.2
      hwords hpc hmem).pre (fun _ h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩)).mono (by omega)
  | div a b c =>
    exact ((RamVirtualBasic.instruction_spec B w .div s a b c hB hlit.1 hlit.2.1 hlit.2.2
      hwords hpc hmem).pre (fun _ h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩)).mono (by omega)
  | and a b c =>
    exact ((RamVirtualBasic.instruction_spec B w .and s a b c hB hlit.1 hlit.2.1 hlit.2.2
      hwords hpc hmem).pre (fun _ h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩)).mono (by omega)
  | shiftl a b c =>
    exact lift (.shiftl a b c) (SparseRam.assign w s a (SparseRam.lookup s.memory (b % 2 ^ w) *
        2 ^ SparseRam.lookup s.memory (c % 2 ^ w))) _ _ trivial ⟨rfl, rfl, rfl⟩
      (RamVirtualBitOps.shift_core_spec B w s.pc s.memory a b c hB hlit.1 hlit.2.1 hlit.2.2 hwords hpc hmem)
      (fun _ h hA hV => ⟨h.1, hA, hV⟩) (by omega)
  | not a b =>
    exact lift (.not a b) (SparseRam.assign w s a (2 ^ w - 1 - SparseRam.lookup s.memory (b % 2 ^ w)))
      _ _ trivial ⟨rfl, rfl, rfl⟩
      (RamVirtualBitOps.not_core_spec B w s.pc s.memory a b h1 hM hlit.1 hlit.2 hwords hpc hmem)
      (fun _ h hA hV => ⟨h.1, hA, hV⟩) (by omega)
  | jump l =>
    exact lift (.jump l) { s with pc := l } 2 _ trivial ⟨rfl, rfl, rfl⟩
      (jump_spec B w s.pc s.memory l hlit) (fun _ h _ _ => h.1) (by omega)
  | jzero a l =>
    exact lift (.jzero a l) { s with pc := if SparseRam.lookup s.memory (a % 2 ^ w) = 0 then l else s.pc + 1 }
      _ _ trivial ⟨rfl, rfl, rfl⟩
      (RamVirtualControl.jzero_core_spec B w s.pc s.memory a l h1 hM hlit.1 hlit.2 hpc (by omega) hwords)
      (fun _ h hA hV => ⟨h.1, hA, hV⟩) (by omega)
  | jeof l =>
    have hj := RamFrames.keep_scalar (RamVirtualControl.jeof_spec B w s l hlit hinput hpc h1)
      "vm.running" 1 (by simp [instruction, increment, Com.wvars])
    exact (hj.pre (fun _ h => ⟨h.1, h.2.1⟩)).mono (by omega)
  | inputLength a =>
    exact lift (.inputLength a) (SparseRam.assign w s a s.input.length) 40 _ trivial ⟨rfl, rfl, rfl⟩
      (RamVirtualInput.length_core_spec B w s.pc s.memory s.input.length a h1 hM hlit hinput hpc hmem)
      (fun _ h hA hV => ⟨⟨h.1, hA, hV⟩, h.2.2.1⟩) (by omega)
  | inputLoad a b =>
    exact lift (.inputLoad a b) (SparseRam.assign w s a
        (s.input[SparseRam.lookup s.memory (b % 2 ^ w) % 2 ^ w]?.getD 0)) _ _ trivial ⟨rfl, rfl, rfl⟩
      (RamVirtualInput.load_core_spec B w s.pc s.memory s.input a b h1 hM hlit.1 hlit.2
        hinput hinputWords hwords hpc hmem)
      (fun _ h hA hV => ⟨⟨h.1, hA, hV⟩, h.2.1, h.2.2.1⟩) (by omega)
  | halt => exact ((stop_spec B w s (by omega)).pre (fun _ h => h.1)).mono (by omega)
  | read a =>
    cases hi : s.inp with
    | nil =>
      simpa only [Result, SparseRam.effect, hi, List.head?_nil, Option.map_none] using
        (((RamVirtualRead.empty_spec B w s a (by omega) hinput hi).pre (fun _ h => h.1)).mono
          (show 6 ≤ 32 * s.memory.length + 100 by omega))
    | cons value rest =>
      simpa only [Result, SparseRam.effect, hi, List.head?_cons, List.tail_cons, Option.map_some] using
        (((RamVirtualRead.nonempty_spec B w s a value rest h1 hM hlit hinput hinputWords hi hpc hmem).pre
          (fun _ h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩)).mono
          (show 51 ≤ 32 * s.memory.length + 100 by omega))
  | write a =>
    exact ((RamVirtualOutput.write_spec B w s a h1 hM hlit hwords hpc (by omega) hout).pre
      (fun _ h => ⟨h.1, h.2.1, h.2.2.2.2⟩)).mono (by omega)

end Lax455465Proofs.RamVirtualInstruction
