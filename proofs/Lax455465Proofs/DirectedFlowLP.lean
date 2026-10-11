import Lax455465.RationalEncoding
import Lax109476.LinearProgram
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic

/-! The polynomial-size edge formulation used by the deterministic solver.
There is one concurrent-value variable and n⁴ commodity/arc variables.
Capacity rows and paired conservation rows give n² + 2n³ inequalities.
No enumeration of simple paths is used in this LP. -/

open scoped BigOperators NNRat

namespace Lax455465Proofs.DirectedFlowLP

open Lax455465.RationalEncoding Lax109476.LinearProgram

abbrev Edge (n : ℕ) := Fin n × Fin n
abbrev CommodityArc (n : ℕ) := Edge n × Edge n
abbrev Balance (n : ℕ) := Edge n × Fin n
abbrev Variable (n : ℕ) := Fin 1 ⊕ CommodityArc n
abbrev Row (n : ℕ) := Edge n ⊕ (Fin 2 × Balance n)

def edgeIndex (n : ℕ) : Edge n ≃ Fin (n * n) := finProdFinEquiv

def arcIndex (n : ℕ) : CommodityArc n ≃ Fin ((n * n) * (n * n)) :=
  ((edgeIndex n).prodCongr (edgeIndex n)).trans finProdFinEquiv

def balanceIndex (n : ℕ) : Balance n ≃ Fin ((n * n) * n) :=
  ((edgeIndex n).prodCongr (Equiv.refl (Fin n))).trans finProdFinEquiv

def variableIndex (n : ℕ) : Variable n ≃ Fin (1 + (n * n) * (n * n)) :=
  ((Equiv.refl (Fin 1)).sumCongr (arcIndex n)).trans finSumFinEquiv

def rowIndex (n : ℕ) : Row n ≃ Fin (n * n + 2 * ((n * n) * n)) :=
  ((edgeIndex n).sumCongr
    (((Equiv.refl (Fin 2)).prodCongr (balanceIndex n)).trans finProdFinEquiv)).trans
      finSumFinEquiv

/-- The signed demand divergence at one vertex. Equal endpoints have zero demand. -/
def divergence {n : ℕ} (I : RationalInstance n) (s t u : Fin n) : ℚ :=
  if s = t then 0 else
    (if u = s then (I.weight s : ℚ) * I.weight t else 0) -
    (if u = t then (I.weight s : ℚ) * I.weight t else 0)

/-- One conservation equation, written as a linear expression equal to zero. -/
def balanceCoefficient {n : ℕ} (I : RationalInstance n)
    (b : Balance n) : Variable n → ℚ
  | .inl _ => - divergence I b.1.1 b.1.2 b.2
  | .inr a => if a.1 = b.1 then
      (if a.2.1 = b.2 then 1 else 0) - (if a.2.2 = b.2 then 1 else 0)
    else 0

/-- Capacity rows followed by both signs of every conservation equation. -/
def coefficient {n : ℕ} (I : RationalInstance n) : Row n → Variable n → ℚ
  | .inl _, .inl _ => 0
  | .inl e, .inr a => if a.2 = e then 1 else 0
  | .inr (sign, b), v =>
      if sign = 0 then balanceCoefficient I b v else -balanceCoefficient I b v

def rowBound {n : ℕ} (I : RationalInstance n) : Row n → ℚ
  | .inl e => I.capacity e.1 e.2
  | .inr _ => 0

def objective {n : ℕ} : Variable n → ℚ
  | .inl _ => 1
  | .inr _ => 0

/-- Dense rational LP with a polynomial number of rows and variables. -/
def program {n : ℕ} (I : RationalInstance n) :
    Program ℚ (n * n + 2 * ((n * n) * n)) (1 + (n * n) * (n * n)) where
  A i j := coefficient I ((rowIndex n).symm i) ((variableIndex n).symm j)
  b i := rowBound I ((rowIndex n).symm i)
  c j := objective ((variableIndex n).symm j)

/-- Interpret typed concurrent-value and arc coordinates as an LP vector. -/
def vector {n : ℕ} (f : ℚ) (x : CommodityArc n → ℚ) :
    Fin (1 + (n * n) * (n * n)) → ℚ :=
  fun j => match (variableIndex n).symm j with
    | .inl _ => f
    | .inr a => x a

/-- The exact directed arc-flow feasibility conditions. -/
def Feasible {n : ℕ} (I : RationalInstance n) (f : ℚ) (x : CommodityArc n → ℚ) : Prop :=
  0 ≤ f ∧ (∀ a, 0 ≤ x a) ∧
  (∀ e : Edge n, (∑ st : Edge n, x (st, e)) ≤ (I.capacity e.1 e.2 : ℚ)) ∧
  ∀ (st : Edge n) (u : Fin n),
    (∑ v, x (st, (u, v))) - (∑ v, x (st, (v, u))) =
      f * divergence I st.1 st.2 u

private theorem sum_variables {n : ℕ} (g : Variable n → ℚ) :
    (∑ j : Fin (1 + (n * n) * (n * n)), g ((variableIndex n).symm j)) =
      g (.inl 0) + ∑ a : CommodityArc n, g (.inr a) := by
  rw [← Equiv.sum_comp (variableIndex n)]
  simp

private theorem capacity_row {n : ℕ} (I : RationalInstance n) (f : ℚ)
    (x : CommodityArc n → ℚ) (e : Edge n) :
    rowValue (program I) (vector f x) (rowIndex n (.inl e)) =
      ∑ st : Edge n, x (st, e) := by
  simp only [rowValue, program, Equiv.symm_apply_apply, vector]
  change (∑ j, (fun v : Variable n => coefficient I (.inl e) v *
    (match v with | .inl _ => f | .inr a => x a)) ((variableIndex n).symm j)) = _
  rw [sum_variables (n := n) (fun v => coefficient I (.inl e) v *
    (match v with | .inl _ => f | .inr a => x a))]
  simp [coefficient, Fintype.sum_prod_type]

private theorem balance_row {n : ℕ} (I : RationalInstance n) (f : ℚ)
    (x : CommodityArc n → ℚ) (b : Balance n) :
    (∑ j : Fin (1 + (n * n) * (n * n)),
      balanceCoefficient I b ((variableIndex n).symm j) * vector f x j) =
      -divergence I b.1.1 b.1.2 b.2 * f +
        ((∑ v, x (b.1, (b.2, v))) - ∑ v, x (b.1, (v, b.2))) := by
  change (∑ j, (fun v : Variable n => balanceCoefficient I b v *
    (match v with | .inl _ => f | .inr a => x a)) ((variableIndex n).symm j)) = _
  rw [sum_variables (n := n) (fun v => balanceCoefficient I b v *
    (match v with | .inl _ => f | .inr a => x a))]
  simp [balanceCoefficient, Fintype.sum_prod_type, sub_mul, Finset.sum_sub_distrib,
    Finset.sum_ite_irrel]
  rw [Finset.sum_comm]
  simp

private theorem positive_balance_row {n : ℕ} (I : RationalInstance n) (f : ℚ)
    (x : CommodityArc n → ℚ) (b : Balance n) :
    rowValue (program I) (vector f x) (rowIndex n (.inr (0, b))) =
      -divergence I b.1.1 b.1.2 b.2 * f +
        ((∑ v, x (b.1, (b.2, v))) - ∑ v, x (b.1, (v, b.2))) := by
  simp only [rowValue, program, Equiv.symm_apply_apply]
  simpa only [coefficient, ite_true] using balance_row I f x b

private theorem negative_balance_row {n : ℕ} (I : RationalInstance n) (f : ℚ)
    (x : CommodityArc n → ℚ) (b : Balance n) :
    rowValue (program I) (vector f x) (rowIndex n (.inr (1, b))) =
      -(-divergence I b.1.1 b.1.2 b.2 * f +
        ((∑ v, x (b.1, (b.2, v))) - ∑ v, x (b.1, (v, b.2)))) := by
  simp only [rowValue, program, Equiv.symm_apply_apply, coefficient]
  have h : (1 : Fin 2) ≠ 0 := by decide
  simp only [if_neg h, neg_mul, Finset.sum_neg_distrib]
  rw [balance_row]
  ring

/-- The edge-flow constraints are exactly the nonnegative LP constraints. -/
theorem feasible_iff {n : ℕ} (I : RationalInstance n) (f : ℚ)
    (x : CommodityArc n → ℚ) :
    PrimalFeasible (program I) (vector f x) ↔ Feasible I f x := by
  constructor
  · rintro ⟨hpos, hrows⟩
    have hf : 0 ≤ f := by simpa [vector] using hpos (variableIndex n (.inl 0))
    have hx : ∀ a, 0 ≤ x a := by
      intro a; simpa [vector] using hpos (variableIndex n (.inr a))
    refine ⟨hf, hx, ?_, ?_⟩
    · intro e
      have h := hrows (rowIndex n (.inl e))
      rw [capacity_row] at h
      simpa only [program, Equiv.symm_apply_apply, rowBound] using h
    · intro st u
      have hp := hrows (rowIndex n (.inr (0, (st, u))))
      have hn := hrows (rowIndex n (.inr (1, (st, u))))
      rw [positive_balance_row] at hp
      rw [negative_balance_row] at hn
      simp only [program, Equiv.symm_apply_apply, rowBound] at hp hn
      linarith
  · rintro ⟨hf, hx, hcap, hbal⟩
    constructor
    · intro j
      simp only [vector]
      cases (variableIndex n).symm j with
      | inl _ => exact hf
      | inr a => exact hx a
    · intro i
      obtain ⟨r, rfl⟩ := (rowIndex n).surjective i
      cases r with
      | inl e =>
        rw [capacity_row]
        simpa only [program, Equiv.symm_apply_apply, rowBound] using hcap e
      | inr b =>
        rcases b with ⟨sign, st, u⟩
        have hzero :
            -divergence I st.1 st.2 u * f +
              ((∑ v, x (st, (u, v))) - ∑ v, x (st, (v, u))) = 0 := by
          rw [hbal]; ring
        have hsign : sign = 0 ∨ sign = 1 := by fin_cases sign <;> simp
        rcases hsign with rfl | rfl
        · rw [positive_balance_row, hzero]
          simp [program, rowBound]
        · rw [negative_balance_row, hzero]
          simp [program, rowBound]

/-- The objective is exactly the concurrent-value coordinate. -/
theorem objective_value {n : ℕ} (I : RationalInstance n) (f : ℚ)
    (x : CommodityArc n → ℚ) : primalValue (program I) (vector f x) = f := by
  simp only [primalValue, program, vector]
  change (∑ j, (fun v : Variable n => objective v *
    (match v with | .inl _ => f | .inr a => x a)) ((variableIndex n).symm j)) = _
  rw [sum_variables (n := n) (fun v => objective v *
    (match v with | .inl _ => f | .inr a => x a))]
  simp [objective]

/-- Every encoded instance has a feasible zero-flow point. -/
theorem zero_feasible {n : ℕ} (I : RationalInstance n) :
    PrimalFeasible (program I) (vector 0 (fun _ => 0)) := by
  rw [feasible_iff]
  refine ⟨le_rfl, fun _ => le_rfl, ?_, ?_⟩
  · intro e
    simp only [Finset.sum_const_zero]
    positivity
  · intro st u
    simp

end Lax455465Proofs.DirectedFlowLP
