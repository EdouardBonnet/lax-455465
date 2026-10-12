import Lax455465Proofs.RamRegionWhole

namespace Lax455465Proofs.RegionRuntimeBounds
open Lax455465.RationalEncoding RegionRuntimeState RamRegionRecord LpInputSize
open scoped NNRat

def HistoryHeight {n : ℕ} (M : ℕ) (s : State n) : Prop := ∀ e∈s.history,Height M (e.radius : ℚ)

/-- Every appended radius is an actual event or grid candidate, so its
rational height is bounded before the history is decoded again. -/
theorem advance_height {n : ℕ} (I : RationalInstance n) (d : MetricMatrix.Matrix n)
    (seed beta delta threshold : ℚ≥0) (p M : ℕ) (s : State n)
    (hM : 1 ≤ M) (hk : RegionBudget.steps p ≤ M)
    (hd : ∀ u v,Height M (d u v : ℚ)) (hdelta : Height M (delta : ℚ))
    (hunit : Height M ((delta/(RegionBudget.steps p : ℚ≥0) : ℚ≥0) : ℚ))
    (hh : HistoryHeight (M*M) s) : HistoryHeight (M*M) (advance I d seed beta delta threshold p s) := by
  cases hs : s.status with
  | large e => simpa only [advance,hs] using hh
  | exhausted => simpa only [advance,hs] using hh
  | failed => simpa only [advance,hs] using hh
  | running =>
    cases hroot : RegionSelection.chooseRoot (RegionLoop.weights I s.active) with
    | none => simpa only [advance,hs,hroot,HistoryHeight] using hh
    | some root =>
      cases hr : radius I d seed beta delta p s.active root with
      | none => simpa only [advance,hs,hroot,hr,HistoryHeight] using hh
      | some r =>
        have hrmem := List.mem_of_find?_eq_some hr
        have hrheight := RadiusData.height (d root) (fun v => d v root) (RegionBudget.steps p) M delta
          hM hk hunit hdelta (hd root) (fun v => hd v root) r hrmem
        simp only [advance,hs,hroot,hr]
        split_ifs
        · exact hh
        · intro e he
          simp only [List.mem_append,List.mem_singleton] at he
          rcases he with he | rfl
          · exact hh e he
          · exact hrheight

theorem iterate_height {n : ℕ} (I : RationalInstance n) (d : MetricMatrix.Matrix n)
    (seed beta delta threshold : ℚ≥0) (p M iterations : ℕ)
    (hM : 1 ≤ M) (hk : RegionBudget.steps p ≤ M)
    (hd : ∀ u v,Height M (d u v : ℚ)) (hdelta : Height M (delta : ℚ))
    (hunit : Height M ((delta/(RegionBudget.steps p : ℚ≥0) : ℚ≥0) : ℚ)) :
    HistoryHeight (M*M) ((advance I d seed beta delta threshold p)^[iterations] (RamRegionBoundedLoop.initial n)) := by
  induction iterations with
  | zero => simp [HistoryHeight,RamRegionBoundedLoop.initial]
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact advance_height I d seed beta delta threshold p M _ hM hk hd hdelta hunit ih

end Lax455465Proofs.RegionRuntimeBounds
