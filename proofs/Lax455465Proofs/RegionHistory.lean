import Lax455465Proofs.RegionLoop
import Lax455465Proofs.BalancedRegionCut

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace Lax455465Proofs.RegionHistory

open Lax455465.RationalEncoding RegionLoop RegionSelection RegionFrontier RegionOrdering

/-- Label by the earliest ball containing the vertex; the final label is
reserved for vertices that were never removed. -/
def index {n : ℕ} (d : RationalDistances.Distance n) :
    (history : List (Region n)) → Fin n → Fin (history.length + 1)
  | [], _ => 0
  | R :: rest, v => if v ∈ R.ball d then 0 else (index d rest v).succ

def orientation {n : ℕ} (history : List (Region n)) (j : ℕ) : Bool :=
  ((history[j]?).map Region.outward).getD true

def activeAt {n : ℕ} (d : RationalDistances.Distance n) :
    Finset (Fin n) → List (Region n) → ℕ → Finset (Fin n)
  | active, [], _ => active
  | active, _ :: _, 0 => active
  | active, R :: rest, j + 1 => activeAt d (active \ R.ball d) rest j

theorem activeAt_zero {n : ℕ} (d : RationalDistances.Distance n)
    (active : Finset (Fin n)) (history : List (Region n)) : activeAt d active history 0 = active := by
  cases history <;> rfl

/-- Runtime residual membership agrees with the earliest-removal labels. -/
theorem activeAt_mem {n : ℕ} (d : RationalDistances.Distance n)
    (history : List (Region n)) (active : Finset (Fin n)) (j : ℕ) (hj : j ≤ history.length) (v : Fin n) :
    v ∈ activeAt d active history j ↔ v ∈ active ∧ j ≤ (index d history v).val := by
  induction history generalizing active j with
  | nil =>
    have hj0 : j = 0 := by simpa using hj
    simp [hj0, activeAt, index]
  | cons R rest ih =>
    cases j with
    | zero => simp [activeAt]
    | succ j =>
      rw [activeAt, ih (active \ R.ball d) j (by simpa using hj)]
      by_cases hv : v ∈ R.ball d
      · simp [index, hv]
      · simp [index, hv]

theorem frontier {n : ℕ} (d : RationalDistances.Distance n) (history : List (Region n))
    (j : ℕ) (hj : j < history.length) (v : Fin n) (ha : j ≤ (index d history v).val) :
    v ∈ history[j].ball d ↔ (index d history v).val = j := by
  induction history generalizing j with
  | nil => simp at hj
  | cons R rest ih =>
    cases j with
    | zero =>
      by_cases hv : v ∈ R.ball d <;> simp [index, hv]
    | succ j =>
      have hnot : v ∉ R.ball d := by
        intro hv
        simp [index, hv] at ha
      have har : j ≤ (index d rest v).val := by
        simpa only [index, if_neg hnot, Fin.val_succ, Nat.succ_le_succ_iff] using ha
      simpa only [List.getElem_cons_succ, index, if_neg hnot, Fin.val_succ,
        Nat.add_right_cancel_iff] using ih j (by simpa using hj) har

theorem step_valid {n : ℕ} (I : RationalInstance n) (d : RationalDistances.Distance n)
    (seed delta : ℚ) (p : ℕ) (history : List (Region n)) (active : Finset (Fin n))
    (hvalid : ValidHistory I d seed delta p active history) (j : ℕ) (hj : j < history.length) :
    StepGood I d seed delta p (activeAt d active history j) history[j] := by
  induction history generalizing active j with
  | nil => simp at hj
  | cons R rest ih =>
    cases j with
    | zero => exact hvalid.1
    | succ j => exact ih (active \ R.ball d) hvalid.2 j (by simpa using hj)

theorem final_support {n : ℕ} (I : RationalInstance n) (d : RationalDistances.Distance n)
    (seed delta : ℚ) (p : ℕ) (history : List (Region n)) (active : Finset (Fin n))
    (hvalid : ValidHistory I d seed delta p active history) :
    (support (weights I (activeAt d active history history.length))).card = 0 := by
  induction history generalizing active with
  | nil => exact hvalid
  | cons R rest ih => exact ih (active \ R.ball d) hvalid.2

theorem capacity_eq_residual {n : ℕ} (I : RationalInstance n) (d : RationalDistances.Distance n)
    (history : List (Region n)) (j : ℕ) (hj : j ≤ history.length) :
    capacity I (activeAt d Finset.univ history j) =
      residual (fun u v => (I.capacity u v : ℚ)) (index d history) j := by
  funext u v
  simp only [capacity, RegionFrontier.residual, activeAt_mem d history Finset.univ j hj,
    Finset.mem_univ, true_and]

theorem activeAt_step {n : ℕ} (d : RationalDistances.Distance n)
    (history : List (Region n)) (active : Finset (Fin n)) (j : ℕ) (hj : j < history.length) :
    activeAt d active history (j + 1) = activeAt d active history j \ history[j].ball d := by
  induction history generalizing active j with
  | nil => simp at hj
  | cons R rest ih =>
    cases j with
    | zero => simp only [activeAt, List.getElem_cons_zero, activeAt_zero]
    | succ j => exact ih (active \ R.ball d) j (by simpa using hj)

theorem orientation_eq {n : ℕ} (history : List (Region n)) (j : ℕ) (hj : j < history.length) :
    orientation history j = history[j].outward := by
  simp only [orientation, List.getElem?_eq_getElem hj, Option.map_some, Option.getD_some]

/-- A block's original mass is exactly the residual mass charged when it
was removed. Earlier overlapping balls have already been disabled. -/
theorem block_mass {n : ℕ} (I : RationalInstance n) (d : RationalDistances.Distance n)
    (history : List (Region n)) (j : Fin history.length) :
    BalancedRegionCut.regionMass I (index d history) j.castSucc =
      ∑ v ∈ history[j.val].ball d, weights I (activeAt d Finset.univ history j.val) v := by
  let A := activeAt d Finset.univ history j.val
  let S := history[j.val].ball d
  have hfull : (∑ v ∈ S, weights I A v) = ∑ v, if v ∈ S then weights I A v else 0 := by
    have hf : Finset.univ.filter (fun v => v ∈ S) = S := by ext v; simp
    rw [← hf, Finset.sum_filter]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  change (∑ v, if index d history v = j.castSucc then (I.weight v : ℚ) else 0) = ∑ v ∈ S, weights I A v
  rw [hfull]
  apply Finset.sum_congr rfl
  intro v _
  have hm : v ∈ A ↔ j.val ≤ (index d history v).val := by
    simpa only [A, Finset.mem_univ, true_and] using
      activeAt_mem d history Finset.univ j.val j.isLt.le v
  have hi : index d history v = j.castSucc ↔ v ∈ A ∧ v ∈ S := by
    constructor
    · intro h
      have hv : (index d history v).val = j.val := congrArg Fin.val h
      have ha : v ∈ A := hm.mpr hv.ge
      exact ⟨ha, (frontier d history j.val j.isLt v hv.ge).mpr hv⟩
    · rintro ⟨ha, hs⟩
      apply Fin.ext
      exact (frontier d history j.val j.isLt v (hm.mp ha)).mp hs
  simp only [hi, weights]
  by_cases ha : v ∈ A <;> by_cases hs : v ∈ S <;> simp [ha, hs]

/-- No positive mass remains in the final block of a completed history. -/
theorem final_block_zero {n : ℕ} (I : RationalInstance n) (d : RationalDistances.Distance n)
    (seed delta : ℚ) (p : ℕ) (history : List (Region n))
    (hvalid : ValidHistory I d seed delta p Finset.univ history) :
    BalancedRegionCut.regionMass I (index d history) (Fin.last history.length) = 0 := by
  have hs := final_support I d seed delta p history Finset.univ hvalid
  have hz : ∀ v, weights I (activeAt d Finset.univ history history.length) v = 0 := by
    intro v
    have hnot : ¬ 0 < weights I (activeAt d Finset.univ history history.length) v := by
      intro hv
      have hm : v ∈ support (weights I (activeAt d Finset.univ history history.length)) := by
        simp [support, hv]
      have hpos := Finset.card_pos.mpr ⟨v, hm⟩
      omega
    exact le_antisymm (le_of_not_gt hnot) (weights_nonnegative I _ v)
  unfold BalancedRegionCut.regionMass
  apply Finset.sum_eq_zero
  intro v _
  split_ifs with hv
  · have hidx : (index d history v).val = history.length := congrArg Fin.val hv
    have ha : v ∈ activeAt d Finset.univ history history.length :=
      (activeAt_mem d history Finset.univ history.length le_rfl v).mpr ⟨Finset.mem_univ _, hidx.ge⟩
    simpa only [weights, if_pos ha] using hz v
  · rfl

/-- All label blocks of a completed small-region history are small,
including the zero-mass final block. -/
theorem blocks_small {n : ℕ} (I : RationalInstance n) (d : RationalDistances.Distance n)
    (seed delta : ℚ) (p : ℕ) (history : List (Region n))
    (hvalid : ValidHistory I d seed delta p Finset.univ history)
    (hM : 0 < LargeBallRounding.total I) :
    ∀ j, BalancedRegionCut.regionMass I (index d history) j <
      (2 / 3 : ℚ) * BalancedRegionCut.total I := by
  intro j
  by_cases hj : j.val < history.length
  · have hstep := step_valid I d seed delta p history Finset.univ hvalid j.val hj
    let i : Fin history.length := ⟨j.val, hj⟩
    have hji : j = i.castSucc := Fin.ext rfl
    rw [hji, block_mass]
    exact hstep.2.2.2.2.2
  · have hlast : j = Fin.last history.length := by apply Fin.ext; have h := j.isLt; simp; omega
    rw [hlast, final_block_zero I d seed delta p history hvalid]
    change 0 < (2 / 3 : ℚ) * LargeBallRounding.total I
    positivity

end Lax455465Proofs.RegionHistory
