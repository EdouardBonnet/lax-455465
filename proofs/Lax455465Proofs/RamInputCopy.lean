import Lax455465Proofs.RamSparseMemory

namespace Lax455465Proofs.RamInputCopy

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

def copyStep : Com := .seq (.read "input.word")
  (.seq (.store "input.data" (.var "input.i") (.var "input.word"))
    (.assign "input.i" (.add (.var "input.i") (.lit 1))))

def Invariant (xs : List ℕ) (σ : Env) : Prop :=
  σ.vars "input.length" = xs.length ∧ σ.vars "input.i" ≤ xs.length ∧
  σ.inp = xs.drop (σ.vars "input.i") ∧ xs.length ≤ (σ.arrs "input.data").length ∧
  ∀ j, j < σ.vars "input.i" → (σ.arrs "input.data")[j]? = xs[j]?

theorem drop_head (xs : List ℕ) (i : ℕ) (hi : i < xs.length) :
    xs.drop i = xs[i] :: xs.drop (i + 1) := by
  exact List.cons_getElem_drop_succ.symm

private theorem prefix_advance (xs buffer : List ℕ) (i : ℕ) (hi : i < xs.length)
    (hbuffer : xs.length ≤ buffer.length) (h : ∀ j, j < i → buffer[j]? = xs[j]?) :
    ∀ j, j < i + 1 → (buffer.set i xs[i])[j]? = xs[j]? := by
  intro j hj
  by_cases he : i = j
  · subst j
    rw [List.getElem?_set_self (by omega), List.getElem?_eq_getElem hi]
  · rw [List.getElem?_set_ne he]
    exact h j (by omega)

theorem copyStep_spec (B : ℕ) (xs : List ℕ) (h1 : 1 < B) (hlen : xs.length < B)
    (hwords : ∀ x ∈ xs, x < B) :
    Spec B (fun σ => Invariant xs σ ∧ σ.vars "input.i" < xs.length) copyStep
      (fun σ τ => Invariant xs τ ∧ τ.vars "input.i" = σ.vars "input.i" + 1) 8 := by
  rintro σ ⟨⟨hcount, hindex, hinp, hlength, harrays⟩, hi⟩
  have hhead := drop_head xs (σ.vars "input.i") hi
  have hv := hwords xs[σ.vars "input.i"] (List.getElem_mem hi)
  rw [hhead] at hinp
  have hnext := prefix_advance xs (σ.arrs "input.data") (σ.vars "input.i") hi hlength harrays
  clear hhead harrays
  run_vcg
  all_goals simp_all [Invariant]

/-- Copy the physical length-prefixed input into a reserved host array.
The logical word list itself may be arbitrary. -/
def copy : Com := .seq (.read "input.length")
  (.seq (.assign "input.i" (.lit 0))
    (.while (.lt (.var "input.i") (.var "input.length")) copyStep))

theorem copy_spec (B : ℕ) (xs : List ℕ) (h1 : 1 < B) (hlen : xs.length < B)
    (hwords : ∀ x ∈ xs, x < B) :
    Spec B (fun σ => σ.inp = xs.length :: xs ∧ xs.length ≤ (σ.arrs "input.data").length) copy
      (fun _ τ => τ.vars "input.length" = xs.length ∧ τ.inp = [] ∧
        ∀ j (hj : j < xs.length), (τ.arrs "input.data")[j]? = some xs[j])
      (12 * xs.length + 7) := by
  have hlo := Spec.forRangeZero "input.i" "input.length" (Invariant xs) xs.length 8 hlen
    (fun _ h => h.2.1) (fun _ h => h.1) (copyStep_spec B xs h1 hlen hwords)
  have hfinish := hlo.post (fun _ τ _ h =>
    (show τ.vars "input.length" = xs.length ∧ τ.inp = [] ∧
      ∀ j (hj : j < xs.length), (τ.arrs "input.data")[j]? = some xs[j] from
      ⟨h.1.1, by simpa only [h.2, List.drop_length] using h.1.2.2.1,
        by
          intro j hj
          have he := h.1.2.2.2.2 j (by simpa only [h.2] using hj)
          simpa only [List.getElem?_eq_getElem hj] using he⟩))
  rintro σ ⟨hinp, hlength⟩
  run_vcg [hfinish]
  all_goals simp_all [Invariant]

end Lax455465Proofs.RamInputCopy
