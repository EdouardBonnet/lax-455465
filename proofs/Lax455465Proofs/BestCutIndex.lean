import Lax455465Proofs.CutScoreData

namespace Lax455465Proofs.BestCutIndex
open scoped NNRat

def next (valid : ℕ → Prop) [DecidablePred valid] (value : ℕ → ℚ≥0) (i : ℕ) : Option ℕ → Option ℕ
  | none => if valid i then some i else none
  | some j => if valid i ∧ value i<value j then some i else some j

def best (valid : ℕ → Prop) [DecidablePred valid] (value : ℕ → ℚ≥0) : ℕ → Option ℕ
  | 0 => none
  | i+1 => next valid value i (best valid value i)

theorem best_none (valid : ℕ → Prop) [DecidablePred valid] (value : ℕ → ℚ≥0) (i : ℕ) :
    best valid value i=none ↔ ∀ j < i, ¬valid j := by
  induction i with
  | zero => simp [best]
  | succ i ih =>
    cases hb : best valid value i with
    | none =>
      have hn := ih.mp hb
      simp only [best,hb,next]
      by_cases hv : valid i
      · simp only [if_pos hv,Option.some_ne_none,false_iff]
        intro h
        exact h i (by omega) hv
      · simp only [if_neg hv,true_iff]
        intro j hj
        by_cases he : j=i
        · simpa only [he] using hv
        · exact hn j (by omega)
    | some j =>
      have hex : ∃ k < i, valid k := by
        by_contra hn
        have hall : ∀ k < i, ¬valid k := by
          intro k hk hv
          exact hn ⟨k,hk,hv⟩
        have hnone := ih.mpr hall
        rw [hb] at hnone
        cases hnone
      simp only [best,hb,next]
      constructor
      · split_ifs <;> intro h <;> cases h
      · intro h
        obtain ⟨k,hk,hv⟩ := hex
        exact False.elim (h k (by omega) hv)

theorem best_sound (valid : ℕ → Prop) [DecidablePred valid] (value : ℕ → ℚ≥0) (i j : ℕ)
    (h : best valid value i=some j) : j < i ∧ valid j := by
  induction i generalizing j with
  | zero => simp [best] at h
  | succ i ih =>
    simp only [best] at h
    cases hb : best valid value i with
    | none =>
      simp only [hb,next] at h
      split_ifs at h with hv
      · have he : i=j := Option.some.inj h
        subst j
        exact ⟨by omega,hv⟩
    | some k =>
      simp only [hb,next] at h
      split_ifs at h with hv
      · have he : i=j := Option.some.inj h
        subst j
        exact ⟨by omega,hv.1⟩
      · have he : k=j := Option.some.inj h
        subst j
        have hs := ih k hb
        exact ⟨by omega,hs.2⟩

/-- The forward strict-improvement scan retains an admissible minimum-ratio
candidate. Equality keeps the earlier candidate, matching deterministic ties. -/
theorem best_minimal (valid : ℕ → Prop) [DecidablePred valid] (value : ℕ → ℚ≥0) (i j k : ℕ)
    (h : best valid value i=some j) (hk : k < i) (hvalid : valid k) : value j≤value k := by
  induction i generalizing j with
  | zero => omega
  | succ i ih =>
    simp only [best] at h
    cases hb : best valid value i with
    | none =>
      have hn := (best_none valid value i).mp hb
      have he : k=i := by
        by_contra he
        exact hn k (by omega) hvalid
      subst k
      simp only [hb,next,if_pos hvalid,Option.some.injEq] at h
      subst j
      exact le_rfl
    | some old =>
      simp only [hb,next] at h
      by_cases hv : valid i ∧ value i<value old
      · rw [if_pos hv] at h
        have he : i=j := Option.some.inj h
        subst j
        by_cases he : k=i
        · subst k; exact le_rfl
        · exact hv.2.le.trans (ih old hb (by omega))
      · rw [if_neg hv] at h
        have he : old=j := Option.some.inj h
        subst j
        by_cases he : k=i
        · subst k
          exact le_of_not_gt (fun hlt => hv ⟨hvalid,hlt⟩)
        · exact ih old hb (by omega)

end Lax455465Proofs.BestCutIndex
