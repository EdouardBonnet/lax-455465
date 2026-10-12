import Lax455465Proofs.RamRegionBoundedLoop

namespace Lax455465Proofs.RegionRuntimeTermination
open Lax455465.RationalEncoding RegionRuntimeState RegionRuntimeProgress
open scoped NNRat

/-- Every transition which remains running appended one successful small
region. A frozen or failed state cannot resume itself. -/
theorem running_history_step {n : ℕ} (I : RationalInstance n) (length : MetricMatrix.Matrix n)
    (seed beta delta threshold : ℚ≥0) (p : ℕ) (s : State n)
    (h : (advance I length seed beta delta threshold p s).status=.running) :
    s.status=.running ∧ (advance I length seed beta delta threshold p s).history.length=s.history.length+1 := by
  cases hstatus : s.status with
  | large e => simp only [advance,hstatus] at h; cases h
  | exhausted => simp only [advance,hstatus] at h; cases h
  | failed => simp only [advance,hstatus] at h; cases h
  | running =>
    cases hroot : RegionSelection.chooseRoot (RegionLoop.weights I s.active) with
    | none => simp only [advance,hstatus,hroot] at h; cases h
    | some root =>
      cases hr : radius I length seed beta delta p s.active root with
      | none => simp only [advance,hstatus,hroot,hr] at h; cases h
      | some r =>
        let q := RadiusSearchData.atRadius (RegionExecutionData.query I length s.active root seed beta) r
        let e := RamSmallRegion.selected q root
        by_cases hl : RamRegionBranch.large q threshold
        · have ha : advance I length seed beta delta threshold p s={s with status := .large e} := by
            simp only [advance,hstatus,hroot,hr]
            change (if RamRegionBranch.large q threshold then _ else _)=_
            rw [if_pos hl]
          rw [ha] at h
          cases h
        · have ha : advance I length seed beta delta threshold p s=
              {active := s.active \ e.region.ball (MetricMatrix.rational length),history := s.history++[e],status := .running} := by
            simp only [advance,hstatus,hroot,hr]
            change (if RamRegionBranch.large q threshold then _ else _)=_
            rw [if_neg hl]
          exact ⟨rfl,by simp only [ha,List.length_append,List.length_singleton]⟩

/-- A still-running state after i iterations has already recorded i small
regions. This is incompatible with the support budget once i exceeds p. -/
theorem running_history_length {n : ℕ} (I : RationalInstance n) (length : MetricMatrix.Matrix n)
    (seed beta delta threshold : ℚ≥0) (p i : ℕ)
    (h : ((advance I length seed beta delta threshold p)^[i] (RamRegionBoundedLoop.initial n)).status=.running) :
    ((advance I length seed beta delta threshold p)^[i] (RamRegionBoundedLoop.initial n)).history.length=i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply'] at h ⊢
    obtain ⟨hp,hlen⟩ := running_history_step I length seed beta delta threshold p _ h
    rw [hlen,ih hp]

/-- The original support budget plus one exhaustion check suffices. -/
theorem not_running {n : ℕ} (I : RationalInstance n) (length : MetricMatrix.Matrix n)
    (seed beta delta threshold : ℚ≥0) (p : ℕ)
    (hbeta : (beta : ℚ)=RegionSearch.slope (RegionBudget.steps p) delta) (hdiag : ∀ v, length v v=0)
    (hsupport : (RegionSelection.support (RegionLoop.weights I Finset.univ)).card≤p) :
    ((advance I length seed beta delta threshold p)^[p+1] (RamRegionBoundedLoop.initial n)).status≠.running := by
  have hb : ∀ i : ℕ, SupportBound I p ((advance I length seed beta delta threshold p)^[i] (RamRegionBoundedLoop.initial n)) := by
    intro i
    induction i with
    | zero => simpa only [SupportBound,RamRegionBoundedLoop.initial,Function.iterate_zero,Function.id_def,List.length_nil,Nat.zero_add] using hsupport
    | succ i ih =>
      rw [Function.iterate_succ_apply']
      exact advance_bound I length seed beta delta threshold p _ hbeta hdiag ih
  intro h
  have hl := running_history_length I length seed beta delta threshold p (p+1) h
  have hh := hb (p+1)
  unfold SupportBound at hh
  rw [hl] at hh
  omega

end Lax455465Proofs.RegionRuntimeTermination
