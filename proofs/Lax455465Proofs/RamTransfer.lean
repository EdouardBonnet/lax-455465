/-
Generic RAM utilities reused from the registered LP development, Apache-2.0:
https://github.com/EdouardBonnet/lax-109476/tree/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864
Only namespaces and imports are adapted here. The LP solver itself is used
through its registered concept theorem, rather than its proof package.
-/
import Lax808846Proofs.Transfer
import Lax759944.RamPolytime
import Mathlib.Algebra.Polynomial.Eval.Defs

namespace Lax455465Proofs.RamTransfer

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Transfer
open Lax759944.BinaryWordEncoding Lax759944.RamPolytime

def physicalInputs : Set (List ℕ) := {tape | ∃ x, tape = x.length :: x}

def layoutAllowance (L : Layout) : ℕ :=
  L.temps + 2 + L.scalars.length + L.arrays.length + 1

theorem layout_fits {L : Layout} {v w : ℕ} (hv : 0 < v)
    (hw : v + layoutAllowance L ≤ w) : L.FitsWords (2 ^ v) w := by
  have hB : 1 < 2 ^ v := Nat.one_lt_pow (ne_of_gt hv) (by decide)
  have hc : layoutAllowance L ≤ 2 ^ layoutAllowance L := Nat.lt_two_pow_self.le
  have hs : max (2 ^ v) (L.span (2 ^ v)) ≤ 2 ^ (v + layoutAllowance L) := by
    rw [pow_add]
    apply max_le
    · exact Nat.le_mul_of_pos_right _ (by positivity)
    · unfold Layout.span
      have hp : 1 ≤ 2 ^ v := hB.le
      calc
        _ ≤ (L.temps + 2 + L.scalars.length) * 2 ^ v + L.arrays.length * 2 ^ v := by
          exact Nat.add_le_add_right (Nat.le_mul_of_pos_right _ hp) _
        _ ≤ layoutAllowance L * 2 ^ v := by unfold layoutAllowance; nlinarith
        _ ≤ _ := by simpa [Nat.mul_comm] using Nat.mul_le_mul_right (2 ^ v) hc
  exact fitsWords_of_max_le hB (hs.trans (Nat.pow_le_pow_right (by decide) hw))

/-- A bounded structured program is transferred to the existing uniform
word-RAM predicate, including its physical length prefix and every larger
word length. No new computation model or algorithmic axiom is introduced. -/
theorem ramPolytime_of_solves (L : Layout) (c : Com) (f : List ℕ → List ℕ)
    (W T : Polynomial ℕ)
    (hW : ∀ x, 0 < W.eval (bitSize x))
    (hfit : ∀ x, FitsInWords (W.eval (bitSize x)) ((x.length :: x) ++ f x))
    (h : Solves L c physicalInputs (fun tape => f tape.tail)
      (fun tape => 2 ^ W.eval (bitSize tape.tail))
      (fun tape => T.eval (bitSize tape.tail))) : RamPolytime f := by
  refine ⟨compileProgram L c, W + Polynomial.C (layoutAllowance L),
    Polynomial.C L.const * T + Polynomial.C 1, ?_⟩
  intro x
  simp only [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul]
  constructor
  · intro a ha
    exact (hfit x a ha).trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_add_right _ _))
  · intro w hw
    obtain ⟨ext, σ', ⟨k, hk, hbs⟩, hout⟩ := h.run (x.length :: x) ⟨x, rfl⟩
    have hi := h.inp (x.length :: x) ⟨x, rfl⟩
    simp only [List.tail_cons] at hi hk hbs hout
    obtain ⟨t, ht, hrun⟩ := Lax808846Proofs.Simulation.compileProgram_runsTo
      (layout_fits (hW x) hw) h.ok hi hbs
    exact ⟨t, ht.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ hk) 1),
      by simpa only [hout] using hrun⟩

end Lax455465Proofs.RamTransfer
