import Lax455465Proofs.RamFrames
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Polynomial.Inductions

namespace Lax455465Proofs.RamPolynomial

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

/-- The list is fixed program data, with coefficients in increasing degree. -/
def value : List ℕ → ℕ → ℕ
  | [], _ => 0
  | a :: rest, x => a + x * value rest x

/-- Horner evaluation is compiled entirely into native integer operations. -/
def command : List ℕ → Com
  | [] => .assign "poly.value" (.lit 0)
  | a :: rest => .seq (command rest)
      (.assign "poly.value" (.add (.lit a) (.mul (.var "poly.argument") (.var "poly.value"))))

theorem argument_frame (coefficients : List ℕ) : "poly.argument" ∉ (command coefficients).wvars := by
  induction coefficients with
  | nil => simp [command, Com.wvars]
  | cons a rest ih => simp [command, Com.wvars, ih]

theorem variable_frame (coefficients : List ℕ) (x : String) (hx : x ≠ "poly.value") :
    x ∉ (command coefficients).wvars := by
  induction coefficients with
  | nil => simp [command, Com.wvars, hx]
  | cons a rest ih => simp [command, Com.wvars, ih, hx]

theorem arrays_frame (coefficients : List ℕ) : (command coefficients).warrs = [] := by
  induction coefficients with
  | nil => simp [command, Com.warrs]
  | cons a rest ih => simp [command, Com.warrs, ih]

theorem value_mono (coefficients : List ℕ) {x y : ℕ} (h : x ≤ y) :
    value coefficients x ≤ value coefficients y := by
  induction coefficients with
  | nil => rfl
  | cons a rest ih => exact Nat.add_le_add_left (Nat.mul_le_mul h ih) a

theorem command_spec (B : ℕ) (coefficients : List ℕ) (x : ℕ)
    (hB : 0 < B) (hx : x < B) (hvalue : value coefficients (x + 1) < B) :
    Spec B (fun σ => σ.vars "poly.argument" = x) (command coefficients)
      (fun _ τ => τ.vars "poly.value" = value coefficients x)
      (6 * coefficients.length + 2) := by
  induction coefficients with
  | nil =>
    intro σ hσ
    run_vcg
    all_goals simp_all [value]
  | cons a rest ih =>
    have htail : value rest (x + 1) ≤ value (a :: rest) (x + 1) := by
      simp only [value]
      nlinarith
    have hrest := ih (htail.trans_lt hvalue)
    have hrest' := RamFrames.keep_scalar hrest "poly.argument" x (argument_frame rest)
    have hsmall := value_mono (a :: rest) (show x ≤ x + 1 by omega)
    have hresult : a + x * value rest x < B := hsmall.trans_lt hvalue
    have ha : a < B := by omega
    have hproduct : x * value rest x < B := by omega
    have htailSmall := value_mono rest (show x ≤ x + 1 by omega)
    have hv : value rest x < B := htailSmall.trans_lt (htail.trans_lt hvalue)
    rintro σ hσ
    run_vcg [hrest']
    all_goals simp_all [value]

/-- Every natural-coefficient polynomial has a fixed finite Horner program;
the coefficients are embedded in that program rather than read from an oracle. -/
theorem exists_coefficients (p : Polynomial ℕ) : ∃ coefficients : List ℕ,
    ∀ x : ℕ, value coefficients x = p.eval x := by
  refine Polynomial.recOnHorner p ?_ ?_ ?_
  · exact ⟨[], fun _ => by simp [value]⟩
  · intro q a _ _ ih
    obtain ⟨coefficients, hcoeff⟩ := ih
    cases coefficients with
    | nil =>
      refine ⟨[a], ?_⟩
      intro x
      rw [Polynomial.eval_add, Polynomial.eval_C, ← hcoeff x]
      simp [value]
    | cons b rest =>
      refine ⟨(b + a) :: rest, ?_⟩
      intro x
      rw [Polynomial.eval_add, Polynomial.eval_C, ← hcoeff x]
      simp only [value]
      omega
  · intro q _ ih
    obtain ⟨coefficients, hcoeff⟩ := ih
    refine ⟨0 :: coefficients, ?_⟩
    intro x
    simp only [value, Nat.zero_add, hcoeff, Polynomial.eval_mul, Polynomial.eval_X, Nat.mul_comm]

theorem exists_command (p : Polynomial ℕ) : ∃ (c : Com) (K : ℕ), ∀ x B : ℕ,
    0 < B → x < B → p.eval (x + 1) < B →
      Spec B (fun σ => σ.vars "poly.argument" = x) c
        (fun _ τ => τ.vars "poly.value" = p.eval x) K := by
  obtain ⟨coefficients, hcoeff⟩ := exists_coefficients p
  refine ⟨command coefficients, 6 * coefficients.length + 2, ?_⟩
  intro x B hB hx hp
  simpa only [hcoeff] using command_spec B coefficients x hB hx (by simpa only [hcoeff] using hp)

end Lax455465Proofs.RamPolynomial
