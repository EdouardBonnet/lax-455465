import Lax455465Proofs.DirectedFlowLP

open scoped BigOperators NNRat

namespace Lax455465Proofs.DirectedFlowDual

open Lax455465.RationalEncoding Lax455465Proofs.DirectedFlowLP Lax109476.LinearProgram

/-- The multiplier on one arc capacity constraint is its dual length. -/
def length {n : ℕ} (y : Fin (n * n + 2 * ((n * n) * n)) → ℚ)
    (u v : Fin n) : ℚ := y (rowIndex n (.inl (u, v)))

/-- Paired conservation multipliers define one signed potential per commodity. -/
def potential {n : ℕ} (y : Fin (n * n + 2 * ((n * n) * n)) → ℚ)
    (st : Edge n) (u : Fin n) : ℚ :=
  y (rowIndex n (.inr (0, (st, u)))) - y (rowIndex n (.inr (1, (st, u))))

/-- The dual objective is the capacity-weighted length sum. -/
theorem objective_eq {n : ℕ} (I : RationalInstance n)
    (y : Fin (n * n + 2 * ((n * n) * n)) → ℚ) :
    dualValue (program I) y = ∑ u, ∑ v, (I.capacity u v : ℚ) * length y u v := by
  unfold dualValue
  rw [← Equiv.sum_comp (rowIndex n)]
  simp [program, rowBound, length, Fintype.sum_sum_type, Fintype.sum_prod_type]

/-- An arc column gives the exact potential-difference constraint. -/
theorem arc_column {n : ℕ} (I : RationalInstance n)
    (y : Fin (n * n + 2 * ((n * n) * n)) → ℚ) (st : Edge n) (u v : Fin n) :
    columnValue (program I) y (variableIndex n (.inr (st, (u, v)))) =
      length y u v + potential y st u - potential y st v := by
  unfold columnValue
  rw [← Equiv.sum_comp (rowIndex n)]
  simp [program, coefficient, balanceCoefficient, potential, length,
    Fintype.sum_sum_type, Fintype.sum_prod_type, Fin.sum_univ_two,
    sub_mul, Finset.sum_sub_distrib, Finset.sum_ite_irrel]
  ring

/-- The value column is precisely the product-weighted endpoint separation. -/
theorem value_column {n : ℕ} (I : RationalInstance n)
    (y : Fin (n * n + 2 * ((n * n) * n)) → ℚ) :
    columnValue (program I) y (variableIndex n (.inl 0)) =
      ∑ st : Edge n, (I.weight st.1 : ℚ) * I.weight st.2 *
        (potential y st st.2 - potential y st st.1) := by
  unfold columnValue
  rw [← Equiv.sum_comp (rowIndex n)]
  simp [program, coefficient, balanceCoefficient, divergence, potential,
    Fintype.sum_sum_type, Fintype.sum_prod_type, Fin.sum_univ_two,
    sub_mul, Finset.sum_sub_distrib, Finset.sum_ite_irrel]
  simp only [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  by_cases hst : s = t
  · subst t; simp
  · simp [hst] <;> ring

/-- A feasible LP dual supplies nonnegative lengths and directed Lipschitz potentials. -/
theorem dual_geometry {n : ℕ} (I : RationalInstance n)
    (y : Fin (n * n + 2 * ((n * n) * n)) → ℚ)
    (hy : DualFeasible (program I) y) :
    (∀ u v, 0 ≤ length y u v) ∧
    (∀ st u v, potential y st v - potential y st u ≤ length y u v) ∧
    1 ≤ ∑ st : Edge n, (I.weight st.1 : ℚ) * I.weight st.2 *
      (potential y st st.2 - potential y st st.1) := by
  refine ⟨fun u v => hy.1 _, ?_, ?_⟩
  · intro st u v
    have h := hy.2 (variableIndex n (.inr (st, (u, v))))
    rw [arc_column] at h
    have hc : (program I).c (variableIndex n (.inr (st, (u, v)))) = 0 := by
      simp [program, objective]
    rw [hc] at h
    linarith
  · have h := hy.2 (variableIndex n (.inl 0))
    rw [value_column] at h
    simpa only [program, Equiv.symm_apply_apply, objective] using h

end Lax455465Proofs.DirectedFlowDual
