import Lax455465Proofs.RamVirtualState
import Lax455465Proofs.RamFrames

namespace Lax455465Proofs.RamWordBuffer

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState

/-- Append to the initialized prefix of a reserved native array. -/
def append (array cursor : String) (value : Expr) : Com :=
  .seq (.store array (.var cursor) value)
    (.assign cursor (.add (.var cursor) (.lit 1)))

private theorem prefix_set (words buffer : List ℕ) (value : ℕ)
    (h : ∀ i (hi : i < words.length), buffer[i]? = some words[i])
    (hroom : words.length < buffer.length) :
    ∀ i (hi : i < (words ++ [value]).length),
      (buffer.set words.length value)[i]? = some (words ++ [value])[i] := by
  intro i hi
  by_cases hlt : i < words.length
  · rw [← List.getElem_append_left' hlt, List.getElem?_set_ne (by omega : words.length ≠ i)]
    exact h i hlt
  · have he : i = words.length := by simp only [List.length_append, List.length_singleton] at hi; omega
    subst i
    simp [List.getElem?_set_self hroom]

/-- A native buffer append uses the actual evaluated value and preserves
all older initialized words, even when the remaining array contains stale data. -/
theorem append_spec (B : ℕ) (array cursor : String) (words : List ℕ) (value : ℕ) (e : Expr)
    (h1 : 1 < B) (hlen : words.length + 1 < B) :
    Spec B (fun σ => Prefix words array σ ∧ σ.vars cursor = words.length ∧
      words.length < (σ.arrs array).length ∧ e.evalB B σ = some value) (append array cursor e)
      (fun _ τ => Prefix (words ++ [value]) array τ ∧ τ.vars cursor = words.length + 1)
      (e.size + 6) := by
  rintro σ ⟨hprefix, hcursor, hroom, he⟩
  have hindex : (Expr.var cursor).evalB B σ = some words.length := by
    rw [evalB_var_iff]
    exact ⟨hcursor.symm, hcursor ▸ (by omega : words.length < B)⟩
  have hstore := Run.store hindex he hroom
  let ν := σ.setArr array words.length value
  have hcounter : (Expr.add (.var cursor) (.lit 1)).evalB B ν = some (words.length + 1) := by
    apply evalB_bin (op := .add) _ (evalB_lit h1) hlen
    rw [evalB_var_iff]
    exact ⟨by simpa [ν] using hcursor.symm, by simp [ν, hcursor]; omega⟩
  have hnext := Run.assign (x := cursor) hcounter
  refine ⟨ν.setVar cursor (words.length + 1), (hstore.seq hnext).mono (by simp [Expr.size]; omega), ?_⟩
  constructor
  · simpa only [Prefix, ν, arrs_setVar, arrs_setArr, if_true] using
      prefix_set words (σ.arrs array) value hprefix hroom
  · simp

end Lax455465Proofs.RamWordBuffer
