import Lax455465Proofs.DirectedFlowLP
import Lax109476.PolynomialTimeSolver

open scoped BigOperators NNRat NNReal

namespace Lax455465Proofs.DirectedFlowBounds

open Lax455465.ProductNetwork Lax455465.RationalEncoding
open Lax455465Proofs.DirectedFlowLP Lax109476.LinearProgram
open Lax109476.RationalCertificates Lax109476.FarkasCertificate
open Lax109476.RecessionDirection

/-- Every LP vector has exactly one typed value/arc representation. -/
theorem vector_representation {n : ℕ}
    (z : Fin (1 + (n * n) * (n * n)) → ℚ) :
    vector (z (variableIndex n (.inl 0)))
      (fun a => z (variableIndex n (.inr a))) = z := by
  funext j
  obtain ⟨v, rfl⟩ := (variableIndex n).surjective j
  cases v with
  | inl i =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp [vector]
  | inr a => simp [vector]

/-- Any individual commodity load is bounded by the capacity of its arc. -/
theorem arc_bounded {n : ℕ} (I : RationalInstance n) (f : ℚ)
    (x : CommodityArc n → ℚ) (h : Feasible I f x) (st e : Edge n) :
    x (st, e) ≤ (I.capacity e.1 e.2 : ℚ) := by
  calc
    x (st, e) ≤ ∑ q : Edge n, x (q, e) :=
      Finset.single_le_sum (fun q _ => h.2.1 (q, e)) (Finset.mem_univ st)
    _ ≤ _ := h.2.2.1 e

/-- A positive-demand source bounds the common flow value by its outgoing capacity. -/
theorem value_mul_demand_le {n : ℕ} (I : RationalInstance n) (f : ℚ)
    (x : CommodityArc n → ℚ) (h : Feasible I f x) (s t : Fin n) (hne : s ≠ t) :
    f * ((I.weight s : ℚ) * I.weight t) ≤ ∑ v, (I.capacity s v : ℚ) := by
  have hbalance := h.2.2.2 (s, t) s
  have hin : 0 ≤ ∑ v, x ((s, t), (v, s)) :=
    Finset.sum_nonneg (fun v _ => h.2.1 ((s, t), (v, s)))
  have hout : (∑ v, x ((s, t), (s, v))) ≤ ∑ v, (I.capacity s v : ℚ) :=
    Finset.sum_le_sum (fun v _ => arc_bounded I f x h (s, t) (s, v))
  simp [divergence, hne] at hbalance
  linarith

/-- Two support vertices supply a strictly positive rational demand. -/
theorem positive_pair {n : ℕ} (I : RationalInstance n) (hp : 2 ≤ supportCount I.weights) :
    ∃ s t : Fin n, s ≠ t ∧ 0 < (I.weight s : ℚ) * I.weight t := by
  classical
  have hcard : 1 < (Finset.univ.filter fun v => 0 < I.weights v).card := by
    change 1 < supportCount I.weights
    omega
  obtain ⟨s, hs, t, ht, hne⟩ := Finset.one_lt_card.mp hcard
  have hsQ : 0 < (I.weight s : ℚ) := by
    have hsR := (Finset.mem_filter.mp hs).2
    change (0 : ℝ≥0) < (I.weight s : ℝ≥0) at hsR
    exact_mod_cast hsR
  have htQ : 0 < (I.weight t : ℚ) := by
    have htR := (Finset.mem_filter.mp ht).2
    change (0 : ℝ≥0) < (I.weight t : ℝ≥0) at htR
    exact_mod_cast htR
  exact ⟨s, t, hne, mul_pos hsQ htQ⟩

/-- The rational feasible values have a finite bound, including disconnected inputs. -/
theorem value_bounded {n : ℕ} (I : RationalInstance n) (hp : 2 ≤ supportCount I.weights) :
    ∃ B : ℚ, ∀ f x, Feasible I f x → f ≤ B := by
  obtain ⟨s, t, hne, hprod⟩ := positive_pair I hp
  refine ⟨(∑ v, (I.capacity s v : ℚ)) / ((I.weight s : ℚ) * I.weight t), ?_⟩
  intro f x h
  exact (le_div_iff₀ hprod).mpr (value_mul_demand_le I f x h s t hne)

/-- Flow LP row bounds are nonnegative, so Farkas multipliers cannot have negative cost. -/
theorem no_infeasibility_certificate {n : ℕ} (I : RationalInstance n)
    (y : Fin (n * n + 2 * ((n * n) * n)) → ℚ) :
    ¬ IsInfeasibilityCertificate (program I) y := by
  intro h
  have hb : ∀ i, 0 ≤ (program I).b i := by
    intro i
    simp only [program]
    cases (rowIndex n).symm i with
    | inl e => exact (I.capacity e.1 e.2).property
    | inr b => exact le_rfl
  have hnonneg : 0 ≤ dualValue (program I) y :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (hb i) (h.1 i))
  exact (not_lt_of_ge hnonneg) h.2.2

/-- Keep the demands, but erase all capacities. -/
def zeroCapacity {n : ℕ} (I : RationalInstance n) : RationalInstance n where
  capacity _ _ := 0
  loopless _ := rfl
  weight := I.weight

private theorem zeroCapacity_matrix {n : ℕ} (I : RationalInstance n) :
    (program (zeroCapacity I)).A = (program I).A := by
  funext i j
  simp only [program]
  cases (rowIndex n).symm i with
  | inl e => cases (variableIndex n).symm j <;> rfl
  | inr b => cases (variableIndex n).symm j <;> rfl

private theorem zeroCapacity_bound {n : ℕ} (I : RationalInstance n) :
    (program (zeroCapacity I)).b = fun _ => 0 := by
  funext i
  simp only [program]
  cases (rowIndex n).symm i <;> rfl

/-- An improving recession direction would be a positive flow in the zero-capacity network. -/
theorem no_improving_direction {n : ℕ} (I : RationalInstance n)
    (hp : 2 ≤ supportCount I.weights)
    (d : Fin (1 + (n * n) * (n * n)) → ℚ) :
    ¬ IsImprovingDirection (program I) d := by
  intro h
  let f := d (variableIndex n (.inl 0))
  let x := fun a => d (variableIndex n (.inr a))
  have hreconstruct : vector f x = d := vector_representation d
  have hd : PrimalFeasible (program (zeroCapacity I)) d := by
    refine ⟨h.1, ?_⟩
    intro i
    rw [zeroCapacity_bound]
    simpa only [rowValue, zeroCapacity_matrix] using h.2.1 i
  rw [← hreconstruct, feasible_iff] at hd
  obtain ⟨s, t, hne, hprod⟩ := positive_pair I hp
  have hf := value_mul_demand_le (zeroCapacity I) f x hd s t hne
  simp [zeroCapacity] at hf
  have hfzero : f ≤ 0 := by nlinarith
  have hobj : primalValue (program I) d = f := by
    rw [← hreconstruct, objective_value]
  have hpos := h.2.2
  rw [hobj] at hpos
  exact (not_lt_of_ge hfzero) hpos

/-- The actual exact LP solver returns a matching primal/dual pair for this flow LP. -/
theorem exact_optimal_pair {n : ℕ} (I : RationalInstance n)
    (hp : 2 ≤ supportCount I.weights) :
    ∃ (f : ℚ) (x : CommodityArc n → ℚ)
      (y : Fin (n * n + 2 * ((n * n) * n)) → ℚ),
      Feasible I f x ∧ DualFeasible (program I) y ∧ f = dualValue (program I) y := by
  obtain ⟨solve, _, hsolve⟩ :=
    Lax109476.PolynomialTimeSolver.exists_exact_polynomial_time_solver
  obtain ⟨cert, _, hvalid⟩ := hsolve _ _ (program I)
  cases cert with
  | optimal z y =>
    rcases hvalid with ⟨hz, hy, hval⟩
    let f := z (variableIndex n (.inl 0))
    let x := fun a => z (variableIndex n (.inr a))
    have hrepr : vector f x = z := vector_representation z
    refine ⟨f, x, y, ?_, hy, ?_⟩
    · rw [← hrepr, feasible_iff] at hz
      exact hz
    · rw [← hrepr, objective_value] at hval
      exact hval
  | infeasible y => exact False.elim (no_infeasibility_certificate I y hvalid)
  | unbounded z d => exact False.elim (no_improving_direction I hp d hvalid.2)

end Lax455465Proofs.DirectedFlowBounds
