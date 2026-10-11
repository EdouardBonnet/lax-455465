import Lax455465Proofs.RamSparseMemory

namespace Lax455465Proofs.RamFrames

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

/-- Structured RAM commands never change the extent of a reserved array. -/
theorem array_length {c : Com} {σ τ : Env} {k : ℕ} (h : BigStep c σ τ k) (a : String) :
    (τ.arrs a).length = (σ.arrs a).length := by
  induction h with
  | skip => rfl
  | assign _ => rfl
  | store _ _ _ => simp only [length_arrs_setArr]
  | seq _ _ ih ih' => rw [ih', ih]
  | ite_true _ _ ih => exact ih
  | ite_false _ _ ih => exact ih
  | while_true _ _ _ ih ih' => rw [ih', ih]
  | while_false _ => rfl
  | read _ => rfl
  | write _ => rfl

theorem run_array_length {B K : ℕ} {c : Com} {σ τ : Env} (h : Run B c σ τ K) (a : String) :
    (τ.arrs a).length = (σ.arrs a).length := by
  obtain ⟨_, _, hs⟩ := h.bigStep
  exact array_length hs a

/-- Retain a concrete scalar invariant through a phase using its syntactic
frame, so the next phase receives the value as an ordinary conjunct. -/
theorem keep_scalar {B K : ℕ} {P : Env → Prop} {Q : Env → Env → Prop} {c : Com}
    (h : Spec B P c Q K) (x : String) (v : ℕ) (hx : x ∉ c.wvars) :
    Spec B (fun σ => P σ ∧ σ.vars x = v) c (fun σ τ => Q σ τ ∧ τ.vars x = v) K := by
  rintro σ ⟨hp, hv⟩
  obtain ⟨τ, hr, hq⟩ := h σ hp
  exact ⟨τ, hr, hq, (hr.frame_var x hx).trans hv⟩

/-- Array storage bounds remain available even through phases that write
to the array's initialized prefix. -/
theorem keep_space {B K : ℕ} {P : Env → Prop} {Q : Env → Env → Prop} {c : Com}
    (h : Spec B P c Q K) (a : String) (used : ℕ) :
    Spec B (fun σ => P σ ∧ used < (σ.arrs a).length) c
      (fun σ τ => Q σ τ ∧ used < (τ.arrs a).length) K := by
  rintro σ ⟨hp, hs⟩
  obtain ⟨τ, hr, hq⟩ := h σ hp
  exact ⟨τ, hr, hq, by rwa [run_array_length hr a]⟩

end Lax455465Proofs.RamFrames
