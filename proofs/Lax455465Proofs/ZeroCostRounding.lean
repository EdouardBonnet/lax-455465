import Lax455465Proofs.LargeBallRounding

open scoped BigOperators

namespace Lax455465Proofs.ZeroCostRounding

open Lax455465.RationalEncoding CutSweeps RationalDistances

def pairs (n : ℕ) : List (Fin n × Fin n) :=
  (List.finRange n).flatMap fun u => (List.finRange n).map fun v => (u, v)

def pairTerm {n : ℕ} (I : RationalInstance n) (d : Distance n) (uv : Fin n × Fin n) : ℚ :=
  (I.weight uv.1 : ℚ) * I.weight uv.2 * d uv.1 uv.2

def choosePair {n : ℕ} (I : RationalInstance n) (d : Distance n) : Option (Fin n × Fin n) :=
  (pairs n).find? fun uv => decide (0 < pairTerm I d uv)

def round {n : ℕ} (I : RationalInstance n) (d : Distance n) : Option (Finset (Fin n)) :=
  (choosePair I d).bind fun uv => PotentialLayers.round I (d uv.1)

theorem pair_correct {n : ℕ} (I : RationalInstance n) (d : Distance n)
    (hsep : 1 ≤ LargeBallRounding.distanceSeparation I d) :
    ∃ uv, choosePair I d = some uv ∧ 0 < pairTerm I d uv := by
  have hex : ∃ u v, 0 < pairTerm I d (u, v) := by
    by_contra hn
    push Not at hn
    have hnonpos : LargeBallRounding.distanceSeparation I d ≤ 0 :=
      Finset.sum_nonpos fun u _ => Finset.sum_nonpos fun v _ => hn u v
    linarith
  cases hs : choosePair I d with
  | none =>
    obtain ⟨u, v, hpos⟩ := hex
    have hmem : (u, v) ∈ pairs n := by
      unfold pairs
      apply List.mem_flatMap.mpr
      exact ⟨u, List.mem_finRange u, List.mem_map.mpr ⟨v, List.mem_finRange v, rfl⟩⟩
    have hfail := List.find?_eq_none.mp hs (u, v) hmem
    simp only [decide_eq_true_eq] at hfail
    exact False.elim (hfail hpos)
  | some uv =>
    exact ⟨uv, rfl, by simpa only [decide_eq_true_eq] using List.find?_some hs⟩

theorem potential_separation {n : ℕ} (I : RationalInstance n) (d : Distance n)
    (uv : Fin n × Fin n) (hd : Nonnegative d) (hdiag : ∀ v, d v v = 0)
    (hpair : 0 < pairTerm I d uv) :
    0 < PotentialLayers.separation I (d uv.1) := by
  have hterm : pairTerm I d uv =
      (I.weight uv.1 : ℚ) * I.weight uv.2 * max (d uv.1 uv.2 - d uv.1 uv.1) 0 := by
    rw [hdiag, sub_zero, max_eq_left (hd _ _)]
    rfl
  have hnn : ∀ u v, 0 ≤ (I.weight u : ℚ) * I.weight v * max (d uv.1 v - d uv.1 u) 0 :=
    fun u v => mul_nonneg (mul_nonneg (NNRat.coe_nonneg _) (NNRat.coe_nonneg _)) (le_max_right _ _)
  have hinner := Finset.single_le_sum (fun v _ => hnn uv.1 v) (Finset.mem_univ uv.2)
  have houter : (∑ v, (I.weight uv.1 : ℚ) * I.weight v * max (d uv.1 v - d uv.1 uv.1) 0) ≤
      PotentialLayers.separation I (d uv.1) :=
    Finset.single_le_sum (fun u _ => Finset.sum_nonneg fun v _ => hnn u v) (Finset.mem_univ uv.1)
  rw [hterm] at hpair
  exact hpair.trans_le (hinner.trans houter)

/-- Positive metric separation still supplies an actual zero-capacity
cut when the metric cost is zero; no positive seed is required. -/
theorem round_correct {n : ℕ} (I : RationalInstance n) (d : Distance n)
    (hd : Nonnegative d) (hdiag : ∀ v, d v v = 0)
    (htri : ∀ u v w, d u w ≤ d u v + d v w)
    (hsep : 1 ≤ LargeBallRounding.distanceSeparation I d)
    (hzero : (∑ u, ∑ v, (I.capacity u v : ℚ) * d u v) = 0) :
    ∃ S, round I d = some S ∧ admissibleQ I S ∧ ratioQ I S ≤ 0 := by
  obtain ⟨uv, huv, hpair⟩ := pair_correct I d hsep
  have hpotential := potential_separation I d uv hd hdiag hpair
  obtain ⟨S, hs, hadm, hratio⟩ := PotentialLayers.round_spec I (d uv.1) hpotential
  refine ⟨S, by simp only [round, huv, Option.bind_some, hs], hadm, hratio.trans ?_⟩
  have hcost := PotentialLayers.edgeCost_le I (d uv.1) d hd
    (fun u v => by linarith [htri uv.1 u v])
  rw [hzero] at hcost
  exact div_nonpos_of_nonpos_of_nonneg hcost hpotential.le

end Lax455465Proofs.ZeroCostRounding
