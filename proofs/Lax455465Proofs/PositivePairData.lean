import Lax455465Proofs.RamPositivePair
import Lax455465Proofs.ZeroCostRounding

namespace Lax455465Proofs.PositivePairData
open Lax455465.RationalEncoding DirectedFlowLP
open scoped NNRat

theorem term_pos {n : ℕ} (I : RationalInstance n) (d : MetricMatrix.Matrix n) (u v : Fin n) :
    0<ZeroCostRounding.pairTerm I (MetricMatrix.rational d) (u,v) ↔
      0<(I.weight u).num ∧ 0<(I.weight v).num ∧ 0<(d u v).num := by
  have hmul (a b : ℚ) (ha : 0≤a) (hb : 0≤b) : 0<a*b ↔ 0<a ∧ 0<b := by
    constructor
    · intro h; constructor <;> by_contra hn <;> push Not at hn <;> nlinarith
    · exact fun h => mul_pos h.1 h.2
  change 0<(I.weight u : ℚ)*(I.weight v : ℚ)*(d u v : ℚ) ↔ _
  rw [hmul _ _ (mul_nonneg (NNRat.coe_nonneg _) (NNRat.coe_nonneg _)) (NNRat.coe_nonneg _),
    hmul _ _ (NNRat.coe_nonneg _) (NNRat.coe_nonneg _)]
  simp only [NNRat.num_pos,NNRat.coe_pos,and_assoc]

theorem predicate_at {n : ℕ} (I : RationalInstance n) (d : MetricMatrix.Matrix n) (u v : Fin n) :
    RamPositivePair.predicate I d (edgeIndex n (u,v)).val=
      decide (0<ZeroCostRounding.pairTerm I (MetricMatrix.rational d) (u,v)) := by
  simp only [RamPositivePair.predicate,dif_pos (edgeIndex n (u,v)).isLt,Fin.eta,Equiv.symm_apply_apply,term_pos]

/-- Positive metric separation guarantees that the bounded native pair scan
finds two positive-weight endpoints at positive directed distance. -/
theorem first_correct {n : ℕ} (I : RationalInstance n) (d : MetricMatrix.Matrix n)
    (hsep : 1≤LargeBallRounding.distanceSeparation I (MetricMatrix.rational d)) :
    ∃ u v,RamFind.first (RamPositivePair.predicate I d) (n*n)=some (edgeIndex n (u,v)).val ∧
      0<ZeroCostRounding.pairTerm I (MetricMatrix.rational d) (u,v) := by
  cases he : RamFind.first (RamPositivePair.predicate I d) (n*n) with
  | none =>
    obtain ⟨uv,huv,hpos⟩ := ZeroCostRounding.pair_correct I (MetricMatrix.rational d) hsep
    have hfail := List.find?_eq_none.mp he (edgeIndex n uv).val (List.mem_range.mpr (edgeIndex n uv).isLt)
    rw [predicate_at I d uv.1 uv.2] at hfail
    simp [hpos] at hfail
  | some i =>
    have hi : i<n*n := List.mem_range.mp (List.mem_of_find?_eq_some he)
    let uv := (edgeIndex n).symm ⟨i,hi⟩
    have hidx : (edgeIndex n uv).val=i := congrArg Fin.val ((edgeIndex n).apply_symm_apply ⟨i,hi⟩)
    have hp := List.find?_some he
    rw [←hidx,predicate_at I d uv.1 uv.2] at hp
    exact ⟨uv.1,uv.2,by simp only [hidx],by simpa only [decide_eq_true_eq] using hp⟩

end Lax455465Proofs.PositivePairData
