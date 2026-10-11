import Lax455465.FlowCutCertificate
import Mathlib.Tactic

open scoped BigOperators NNRat NNReal

namespace Lax455465Proofs.CutSweeps

open Lax455465.ProductNetwork Lax455465.RationalEncoding

/-- Rational cut quantities used by the algorithm, without real comparisons. -/
def massQ {n : ℕ} (I : RationalInstance n) (S : Finset (Fin n)) : ℚ :=
  ∑ v ∈ S, (I.weight v : ℚ)

def capacityQ {n : ℕ} (I : RationalInstance n) (S : Finset (Fin n)) : ℚ :=
  ∑ u ∈ S, ∑ v ∈ Sᶜ, (I.capacity u v : ℚ)

def admissibleQ {n : ℕ} (I : RationalInstance n) (S : Finset (Fin n)) : Prop :=
  0 < massQ I S ∧ 0 < massQ I Sᶜ

instance {n : ℕ} (I : RationalInstance n) (S : Finset (Fin n)) :
    Decidable (admissibleQ I S) := inferInstanceAs (Decidable (_ ∧ _))

def ratioQ {n : ℕ} (I : RationalInstance n) (S : Finset (Fin n)) : ℚ :=
  capacityQ I S / (massQ I S * massQ I Sᶜ)

theorem massQ_nonneg {n : ℕ} (I : RationalInstance n) (S : Finset (Fin n)) :
    0 ≤ massQ I S := by
  exact Finset.sum_nonneg (fun v _ => NNRat.coe_nonneg (I.weight v))

theorem capacityQ_nonneg {n : ℕ} (I : RationalInstance n) (S : Finset (Fin n)) :
    0 ≤ capacityQ I S := by
  exact Finset.sum_nonneg (fun u _ => Finset.sum_nonneg
    (fun v _ => NNRat.coe_nonneg (I.capacity u v)))

theorem admissibleQ_iff_product_pos {n : ℕ} (I : RationalInstance n)
    (S : Finset (Fin n)) :
    admissibleQ I S ↔ 0 < massQ I S * massQ I Sᶜ := by
  constructor
  · rintro ⟨hS, hSc⟩
    exact mul_pos hS hSc
  · intro h
    have hS := massQ_nonneg I S
    have hSc := massQ_nonneg I Sᶜ
    constructor <;> nlinarith

theorem demand_zero_of_not_admissible {n : ℕ} (I : RationalInstance n)
    (S : Finset (Fin n)) (h : ¬ admissibleQ I S) :
    massQ I S * massQ I Sᶜ = 0 := by
  have hnonneg := mul_nonneg (massQ_nonneg I S) (massQ_nonneg I Sᶜ)
  have hnot : ¬ 0 < massQ I S * massQ I Sᶜ := by
    simpa only [admissibleQ_iff_product_pos] using h
  exact le_antisymm (le_of_not_gt hnot) hnonneg

/-- Deterministically retain a minimum-ratio admissible cut from a candidate list. -/
def choose {n : ℕ} (I : RationalInstance n) : List (Finset (Fin n)) → Option (Finset (Fin n))
  | [] => none
  | S :: rest =>
    match choose I rest with
    | none => if admissibleQ I S then some S else none
    | some T =>
      if admissibleQ I S ∧ ratioQ I S ≤ ratioQ I T then some S else some T

/-- Every chosen cut belongs to the supplied list and has positive demand. -/
theorem choose_sound {n : ℕ} (I : RationalInstance n)
    (candidates : List (Finset (Fin n))) (S : Finset (Fin n))
    (h : choose I candidates = some S) : S ∈ candidates ∧ admissibleQ I S := by
  induction candidates with
  | nil => simp [choose] at h
  | cons T rest ih =>
    simp only [choose] at h
    split at h
    · split at h
      · simp only [Option.some.injEq] at h
        subst S
        exact ⟨List.mem_cons_self, by assumption⟩
      · simp at h
    · rename_i U hU
      split at h
      · simp only [Option.some.injEq] at h
        subst S
        exact ⟨List.mem_cons_self, (by assumption : admissibleQ I T ∧ _).1⟩
      · simp only [Option.some.injEq] at h
        subst S
        obtain ⟨hmem, hadm⟩ := ih hU
        exact ⟨List.mem_cons_of_mem _ hmem, hadm⟩

/-- If there is an admissible candidate, the deterministic selection succeeds. -/
theorem choose_exists {n : ℕ} (I : RationalInstance n)
    (candidates : List (Finset (Fin n)))
    (hex : ∃ S ∈ candidates, admissibleQ I S) : ∃ S, choose I candidates = some S := by
  induction candidates with
  | nil => simp at hex
  | cons T rest ih =>
    by_cases hrest : ∃ S ∈ rest, admissibleQ I S
    · obtain ⟨U, hU⟩ := ih hrest
      simp only [choose, hU]
      split <;> exact ⟨_, rfl⟩
    · have hnone : choose I rest = none := by
        cases h : choose I rest with
        | none => rfl
        | some U =>
          obtain ⟨hmem, hadm⟩ := choose_sound I rest U h
          exact False.elim (hrest ⟨U, hmem, hadm⟩)
      obtain ⟨S, hmem, hadm⟩ := hex
      rcases List.mem_cons.mp hmem with rfl | hmem
      · exact ⟨S, by simp [choose, hnone, hadm]⟩
      · exact False.elim (hrest ⟨S, hmem, hadm⟩)

/-- The chosen cut has ratio no greater than any admissible candidate. -/
theorem choose_minimal {n : ℕ} (I : RationalInstance n)
    (candidates : List (Finset (Fin n))) (S T : Finset (Fin n))
    (h : choose I candidates = some S) (hT : T ∈ candidates)
    (hvalid : admissibleQ I T) : ratioQ I S ≤ ratioQ I T := by
  induction candidates generalizing S with
  | nil => simp at hT
  | cons U rest ih =>
    simp only [choose] at h
    split at h
    · rename_i hnone
      split at h
      · simp only [Option.some.injEq] at h
        subst S
        rcases List.mem_cons.mp hT with rfl | hT
        · exact le_rfl
        · obtain ⟨V, hV⟩ := choose_exists I rest ⟨T, hT, hvalid⟩
          rw [hnone] at hV
          cases hV
      · simp at h
    · rename_i V hV
      split at h
      · rename_i hbetter
        simp only [Option.some.injEq] at h
        subst S
        rcases List.mem_cons.mp hT with rfl | hT
        · exact le_rfl
        · exact hbetter.2.trans (ih V hV hT)
      · rename_i hnot
        simp only [Option.some.injEq] at h
        subst S
        rcases List.mem_cons.mp hT with rfl | hT
        · exact le_of_not_ge (fun hle => hnot ⟨hvalid, hle⟩)
        · exact ih V hV hT

/-- At most n threshold shores for a rational vertex potential. -/
def candidates {n : ℕ} (potential : Fin n → ℚ) : List (Finset (Fin n)) :=
  (List.finRange n).map fun v => Finset.univ.filter fun u => potential u ≤ potential v

/-- A sweep uses exactly n candidate thresholds; ties may give duplicate shores. -/
theorem candidates_length {n : ℕ} (potential : Fin n → ℚ) :
    (candidates potential).length = n := by
  simp [candidates]

def sweep {n : ℕ} (I : RationalInstance n) (potential : Fin n → ℚ) :
    Option (Finset (Fin n)) := choose I (candidates potential)

/-- Rational cut arithmetic agrees exactly with the real specification. -/
theorem massQ_cast {n : ℕ} (I : RationalInstance n) (S : Finset (Fin n)) :
    (massQ I S : ℝ) = (mass I.weights S : ℝ) := by
  simp [massQ, mass, RationalInstance.weights]
  rfl

theorem capacityQ_cast {n : ℕ} (I : RationalInstance n) (S : Finset (Fin n)) :
    (capacityQ I S : ℝ) = (cutCapacity I.network S : ℝ) := by
  simp [capacityQ, cutCapacity, RationalInstance.network]
  rfl

theorem ratioQ_cast {n : ℕ} (I : RationalInstance n) (S : Finset (Fin n)) :
    (ratioQ I S : ℝ) = (ratioCost I.network I.weights S : ℝ) := by
  simp only [ratioQ, Rat.cast_div, Rat.cast_mul, massQ_cast, capacityQ_cast,
    ratioCost, NNReal.coe_div, NNReal.coe_mul]

theorem admissibleQ_iff {n : ℕ} (I : RationalInstance n) (S : Finset (Fin n)) :
    admissibleQ I S ↔ AdmissibleCut I.weights S := by
  simp only [admissibleQ, AdmissibleCut, ← NNReal.coe_pos, ← massQ_cast]
  norm_cast

end Lax455465Proofs.CutSweeps
