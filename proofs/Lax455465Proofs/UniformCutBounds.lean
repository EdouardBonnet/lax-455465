import Lax455465Proofs.LargeBallRounding
import Lax455465.ShortPathFlow

open scoped BigOperators NNRat NNReal
namespace Lax455465Proofs.UniformCutBounds
open Lax455465.RationalEncoding Lax455465.ProductNetwork CutSweeps

/-- A rational lower bound on every positive-demand cut. -/
def CutLower {n : ℕ} (I : RationalInstance n) (s : ℚ) : Prop :=
  ∀ S, admissibleQ I S → s ≤ ratioQ I S

/-- The finite threshold sweep gives the coarea inequality directly. -/
theorem coarea {n : ℕ} (I : RationalInstance n) (s : ℚ) (hs : CutLower I s)
    (a : Fin n → ℚ) : s * PotentialLayers.separation I a ≤ PotentialLayers.edgeCost I a := by
  have hsep : 0 ≤ PotentialLayers.separation I a :=
    Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun v _ =>
      mul_nonneg (mul_nonneg (NNRat.coe_nonneg _) (NNRat.coe_nonneg _)) (le_max_right _ _)
  by_cases hz : PotentialLayers.separation I a=0
  · rw [hz,mul_zero]
    exact Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun v _ =>
      mul_nonneg (NNRat.coe_nonneg _) (le_max_right _ _)
  · obtain ⟨S,_,hS,hr⟩ := PotentialLayers.round_spec I a (lt_of_le_of_ne hsep (Ne.symm hz))
    exact (le_div_iff₀ (lt_of_le_of_ne hsep (Ne.symm hz))).mp ((hs S hS).trans hr)

theorem uniform_mass {n : ℕ} (I : RationalInstance n) (hw : ∀ v,I.weight v=1)
    (S : Finset (Fin n)) : LargeBallRounding.mass I S=(S.card : ℚ) := by
  simp [LargeBallRounding.mass,hw]

/-- A nonnegative potential vanishing on a large set has its total size
controlled by the capacity-weighted positive differences. -/
theorem large_set_coarea {n : ℕ} (I : RationalInstance n) (hw : ∀ v,I.weight v=1)
    (s : ℚ) (hs : 0 ≤ s) (hcut : CutLower I s) (T : Finset (Fin n))
    (a : Fin n → ℚ) (ha : ∀ v,0 ≤ a v) (hzero : ∀ v∈T,a v=0) :
    s*(T.card : ℚ)*(∑ v,a v) ≤ PotentialLayers.edgeCost I a := by
  have hsep := LargeBallRounding.separation_lower I a T ha hzero
  rw [uniform_mass I hw] at hsep
  simp only [hw,NNRat.coe_one,one_mul] at hsep
  exact (by nlinarith [mul_le_mul_of_nonneg_left hsep hs] :
    s*(T.card : ℚ)*(∑ v,a v) ≤ s*PotentialLayers.separation I a).trans (coarea I s hcut a)

/-- Sparsest cut is below each rational admissible ratio. -/
theorem sparsest_le {n : ℕ} (I : RationalInstance n) (S : Finset (Fin n))
    (hS : admissibleQ I S) : (sparsestCut I.network I.weights : ℝ) ≤ (ratioQ I S : ℝ) := by
  rw [ratioQ_cast]
  exact_mod_cast (csInf_le (OrderBot.bddBelow _) ⟨S,(admissibleQ_iff I S).mp hS,rfl⟩ :
    sparsestCut I.network I.weights ≤ ratioCost I.network I.weights S)

theorem uniform_total {n : ℕ} (I : RationalInstance n) (hw : ∀ v,I.weight v=1) :
    LargeBallRounding.total I=(n : ℚ) := by simp [LargeBallRounding.total,hw]

theorem singleton_admissible {n : ℕ} (I : RationalInstance n) (hw : ∀ v,I.weight v=1)
    (hn : 2 ≤ n) (v : Fin n) : admissibleQ I {v} := by
  constructor
  · simp [massQ,hw]
  · simp only [massQ,hw,NNRat.coe_one,Finset.sum_const,Finset.card_compl,
      Finset.card_singleton,Fintype.card_fin,nsmul_eq_mul,mul_one]
    have : 0 < n-1 := by omega
    exact_mod_cast this

theorem singleton_denominator {n : ℕ} (I : RationalInstance n) (hw : ∀ v,I.weight v=1)
    (hn : 2 ≤ n) (v : Fin n) : massQ I {v}*massQ I ({v}ᶜ)=(n : ℚ)-1 := by
  simp [massQ,hw,Finset.card_compl,Nat.cast_sub (show 1 ≤ n by omega)]

theorem singleton_capacity_le {n : ℕ} (I : RationalInstance n) (v : Fin n) :
    capacityQ I {v} ≤ ∑ u,(I.capacity v u : ℚ) := by
  simp only [capacityQ,Finset.sum_singleton]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun u _ _ => NNRat.coe_nonneg _)

/-- Singleton cuts bound the normalized expansion by the maximum incident
capacity, which is also the parameter in the short-path theorem. -/
theorem expansion_bound {n : ℕ} (I : RationalInstance n) (hw : ∀ v,I.weight v=1)
    (hn : 2 ≤ n) (s R : ℚ) (hcut : CutLower I s)
    (hrows : ∀ v,(∑ u,(I.capacity v u : ℚ)) ≤ R) : s*((n : ℚ)-1) ≤ R := by
  let v : Fin n := ⟨0,by omega⟩
  have h := hcut {v} (singleton_admissible I hw hn v)
  simp only [ratioQ,singleton_denominator I hw hn v] at h
  have hnq : (1 : ℚ) < n := by exact_mod_cast hn
  exact ((le_div_iff₀ (by linarith : (0 : ℚ) < n-1)).mp h).trans
    ((singleton_capacity_le I v).trans (hrows v))

/-- Positive cut expansion forces some genuine edge to have positive capacity. -/
theorem positive_edge {n : ℕ} (I : RationalInstance n) (hw : ∀ v,I.weight v=1)
    (hn : 2 ≤ n) (s : ℚ) (hs : 0 < s) (hcut : CutLower I s) :
    ∃ u v,u ≠ v ∧ 0 < (I.capacity u v : ℚ) := by
  let u : Fin n := ⟨0,by omega⟩
  have h := hcut {u} (singleton_admissible I hw hn u)
  simp only [ratioQ,singleton_denominator I hw hn u] at h
  have hnq : (1 : ℚ) < n := by exact_mod_cast hn
  have hc : 0 < capacityQ I {u} := by
    have hh := (le_div_iff₀ (by linarith : (0 : ℚ) < n-1)).mp h
    have := mul_pos hs (show (0 : ℚ) < n-1 by linarith)
    linarith
  have hrow := hc.trans_le (singleton_capacity_le I u)
  obtain ⟨v,_,hv⟩ := (Finset.sum_pos_iff_of_nonneg (fun v _ => NNRat.coe_nonneg (I.capacity u v))).mp hrow
  refine ⟨u,v,?_,hv⟩
  intro he
  subst v
  simp [I.loopless] at hv

end Lax455465Proofs.UniformCutBounds
