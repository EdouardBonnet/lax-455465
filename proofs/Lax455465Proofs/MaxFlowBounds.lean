import Lax455465Proofs.PathFlowSums

open scoped BigOperators NNReal
namespace Lax455465Proofs.MaxFlowBounds
open Lax455465.ProductNetwork Lax455465.ConcurrentFlow

theorem routed_le_outgoing {n : ℕ} (F : PathFlow n) (s t : Fin n) (hst : s ≠ t) :
    routed F s t ≤ ∑ v, arcLoad F s v := by
  classical
  calc
    routed F s t ≤ ∑ P ∈ F.support,
        F P * ∑ v, ((P.zip P.tail).count (s,v) : ℝ≥0) := by
      apply Finset.sum_le_sum
      intro P _
      by_cases h : P.head? = some s ∧ P.getLast? = some t
      · obtain ⟨v, hv⟩ := PathCounting.first_edge h.1 h.2 hst
        have hcount : (1 : ℝ≥0) ≤ ((P.zip P.tail).count (s,v) : ℝ≥0) := by
          exact_mod_cast Nat.succ_le_iff.mpr (List.count_pos_iff.mpr hv)
        have hsum : (1 : ℝ≥0) ≤ ∑ w, ((P.zip P.tail).count (s,w) : ℝ≥0) :=
          hcount.trans (Finset.single_le_sum
            (f := fun w => ((P.zip P.tail).count (s,w) : ℝ≥0))
            (fun _ _ => bot_le) (Finset.mem_univ v))
        simpa only [if_pos h, mul_one] using mul_le_mul_of_nonneg_left hsum (show 0 ≤ F P from bot_le)
      · simp only [if_neg h]
        exact bot_le
    _ = ∑ v, ∑ P ∈ F.support, F P * ((P.zip P.tail).count (s,v) : ℝ≥0) := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = ∑ v, arcLoad F s v := rfl

theorem value_bound {n : ℕ} (kind : EdgeKind) (N : Network n) (π : VertexWeight n)
    (f : ℝ≥0) (F : PathFlow n) (hF : IsConcurrentFlow kind N π f F)
    (s t : Fin n) (hst : s ≠ t) (hd : 0 < pairDemand kind π s t) :
    f ≤ (∑ v, N.capacity s v) / pairDemand kind π s t := by
  apply (le_div_iff₀ hd).mpr
  calc
    f * pairDemand kind π s t ≤ routed F s t := hF.2.2 s t hst
    _ ≤ ∑ v, arcLoad F s v := routed_le_outgoing F s t hst
    _ ≤ ∑ v, N.capacity s v := by
      apply Finset.sum_le_sum
      intro v _
      apply le_trans _ (hF.2.1 s v)
      cases kind with
      | directed => exact le_rfl
      | undirected => exact le_add_of_nonneg_right bot_le

/-- Two positive-weight vertices bound all real-valued feasible path-flow values. -/
theorem bounded_values {n : ℕ} (kind : EdgeKind) (N : Network n) (π : VertexWeight n)
    (hp : 2 ≤ supportCount π) :
    BddAbove {f | ∃ F : PathFlow n, IsConcurrentFlow kind N π f F} := by
  classical
  obtain ⟨s, hs, t, ht, hst⟩ := Finset.one_lt_card.mp
    (show 1 < (Finset.univ.filter fun v => 0 < π v).card from lt_of_lt_of_le (by decide) hp)
  have hspos : 0 < π s := (Finset.mem_filter.mp hs).2
  have htpos : 0 < π t := (Finset.mem_filter.mp ht).2
  have hd : 0 < pairDemand kind π s t := by
    cases kind <;> simp only [pairDemand] <;> positivity
  refine ⟨(∑ v, N.capacity s v) / pairDemand kind π s t, ?_⟩
  intro f hf
  obtain ⟨F, hF⟩ := hf
  exact value_bound kind N π f F hF s t hst hd

end Lax455465Proofs.MaxFlowBounds
