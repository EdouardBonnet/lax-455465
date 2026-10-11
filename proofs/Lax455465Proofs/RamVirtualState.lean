import Lax455465Proofs.RamVirtualCore

namespace Lax455465Proofs.RamVirtualState

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualCore RamVirtualProgram

/-- Reserved arrays are represented by their initialized prefix, so stale
entries beyond the logical length cannot affect virtual execution. -/
def Prefix (words : List ℕ) (array : String) (σ : Env) : Prop :=
  ∀ i (hi : i < words.length), (σ.arrs array)[i]? = some words[i]

def Tapes (s : SparseRam.SparseState) (σ : Env) : Prop :=
  Prefix s.input "vm.input" σ ∧ σ.vars "vm.inputLength" = s.input.length ∧
  σ.vars "vm.cursor" ≤ s.input.length ∧ s.inp = s.input.drop (σ.vars "vm.cursor") ∧
  Prefix s.out "vm.output" σ ∧ σ.vars "vm.outputLength" = s.out.length

def Represents (w : ℕ) (s : SparseRam.SparseState) (σ : Env) : Prop :=
  Core w s.pc s.memory σ ∧ Tapes s σ

/-- Resetting the logical buffer lengths gives the standard zero-memory
virtual initial state without scanning or clearing the address space. -/
theorem init_spec (B w : ℕ) (input : List ℕ) (h1 : 1 < B) :
    Spec B (fun σ => σ.vars "vm.modulus" = 2 ^ w ∧ σ.vars "vm.width" = w ∧
      Prefix input "vm.input" σ ∧ σ.vars "vm.inputLength" = input.length) initCommand
      (fun _ τ => Represents w (SparseRam.init input) τ ∧ τ.vars "vm.running" = 1) 10 := by
  rintro σ ⟨hM, hw, hp, hlen⟩
  run_vcg
  all_goals simp_all [Represents, Core, Tapes, RamSparseRead.Representation, Prefix, SparseRam.init]

/-- A stop affects only the host's running flag. -/
theorem stop_spec (B w : ℕ) (s : SparseRam.SparseState) (hB : 0 < B) :
    Spec B (Represents w s) stop
      (fun _ τ => Represents w s τ ∧ τ.vars "vm.running" = 0) 2 := by
  rintro σ ⟨hcore, htapes⟩
  run_vcg
  all_goals simp_all [Represents, Core, Tapes, RamSparseRead.Representation, Prefix]

/-- Native phases that leave the virtual tape buffers and counters framed
also preserve the precise sequential and indexed views of virtual input. -/
theorem tapes_frame {B K : ℕ} {c : Com} {σ τ : Env} (hr : Run B c σ τ K)
    (s : SparseRam.SparseState) (ht : Tapes s σ)
    (hinput : "vm.input" ∉ c.warrs) (houtput : "vm.output" ∉ c.warrs)
    (hinlen : "vm.inputLength" ∉ c.wvars) (hcursor : "vm.cursor" ∉ c.wvars)
    (houtlen : "vm.outputLength" ∉ c.wvars) : Tapes s τ := by
  have hi := hr.frame_arr "vm.input" hinput
  have ho := hr.frame_arr "vm.output" houtput
  have hl := hr.frame_var "vm.inputLength" hinlen
  have hc := hr.frame_var "vm.cursor" hcursor
  have hol := hr.frame_var "vm.outputLength" houtlen
  simpa only [Tapes, Prefix, hi, ho, hl, hc, hol] using ht

theorem empty_iff_cursor (s : SparseRam.SparseState) (σ : Env) (h : Tapes s σ) :
    s.inp = [] ↔ σ.vars "vm.cursor" = s.input.length := by
  rw [h.2.2.2.1, List.drop_eq_nil_iff]
  have hb := h.2.2.1
  omega

end Lax455465Proofs.RamVirtualState
