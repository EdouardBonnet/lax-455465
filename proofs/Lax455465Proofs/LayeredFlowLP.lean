import Lax455465Proofs.DirectedFlowLP

open scoped BigOperators NNRat
namespace Lax455465Proofs.LayeredFlowLP
open Lax455465.RationalEncoding Lax109476.LinearProgram
abbrev Edge (n : ℕ) := Fin n × Fin n
abbrev Arc (n L : ℕ) := Edge n × (Fin L × Edge n)
abbrev Balance (n L : ℕ) := Edge n × (Fin (L+1) × Fin n)
abbrev Variable (n L : ℕ) := Fin 1 ⊕ Arc n L
abbrev Row (n L : ℕ) := Edge n ⊕ (Fin 2 × Balance n L)

def arcIndex (n L : ℕ) : Arc n L ≃ Fin ((n*n)*(L*(n*n))) :=
  ((DirectedFlowLP.edgeIndex n).prodCongr
    (((Equiv.refl (Fin L)).prodCongr (DirectedFlowLP.edgeIndex n)).trans finProdFinEquiv)).trans finProdFinEquiv

def balanceIndex (n L : ℕ) : Balance n L ≃ Fin ((n*n)*((L+1)*n)) :=
  ((DirectedFlowLP.edgeIndex n).prodCongr finProdFinEquiv).trans finProdFinEquiv

def variableIndex (n L : ℕ) : Variable n L ≃ Fin (1+(n*n)*(L*(n*n))) :=
  ((Equiv.refl (Fin 1)).sumCongr (arcIndex n L)).trans finSumFinEquiv

def rowIndex (n L : ℕ) : Row n L ≃ Fin (n*n+2*((n*n)*((L+1)*n))) :=
  ((DirectedFlowLP.edgeIndex n).sumCongr
    (((Equiv.refl (Fin 2)).prodCongr (balanceIndex n L)).trans finProdFinEquiv)).trans finSumFinEquiv

/-- Half a unit of supply for each distinct ordered pair, from level zero
at its source to level L at its target. -/
def divergence {n L : ℕ} (b : Balance n L) : ℚ :=
  if b.1.1=b.1.2 then 0 else
    (if b.2.1=0 ∧ b.2.2=b.1.1 then 1/2 else 0) -
    (if b.2.1=Fin.last L ∧ b.2.2=b.1.2 then 1/2 else 0)

/-- An arc advances precisely one level; equal endpoints are free waiting
steps and permit a path shorter than the layer budget. -/
def incidence {n L : ℕ} (b : Balance n L) (a : Arc n L) : ℚ :=
  if a.1=b.1 then
    (if a.2.1.castSucc=b.2.1 ∧ a.2.2.1=b.2.2 then 1 else 0) -
    (if a.2.1.succ=b.2.1 ∧ a.2.2.2=b.2.2 then 1 else 0)
  else 0

/-- Both directions and all levels use the same undirected capacity.
Waiting steps use no capacity. -/
def usage {n L : ℕ} (e : Edge n) (a : Arc n L) : ℚ :=
  if e.1=e.2 then 0 else
    (if a.2.2=e then 1 else 0)+(if a.2.2=(e.2,e.1) then 1 else 0)

def balanceCoefficient {n L : ℕ} (b : Balance n L) : Variable n L → ℚ
  | .inl _ => -divergence b
  | .inr a => incidence b a

def coefficient {n L : ℕ} : Row n L → Variable n L → ℚ
  | .inl _, .inl _ => 0
  | .inl e, .inr a => usage e a
  | .inr (sign,b), v => if sign=0 then balanceCoefficient b v else -balanceCoefficient b v

def rowBound {n L : ℕ} (I : RationalInstance n) : Row n L → ℚ
  | .inl e => I.capacity e.1 e.2
  | .inr _ => 0

def objective {n L : ℕ} : Variable n L → ℚ
  | .inl _ => 1
  | .inr _ => 0

/-- A polynomial-size LP for paths of at most L edges, with capacities
shared across layers. Setting L ≤ n−1 gives at most n⁵+1 variables. -/
def program {n : ℕ} (I : RationalInstance n) (L : ℕ) :
    Program ℚ (n*n+2*((n*n)*((L+1)*n))) (1+(n*n)*(L*(n*n))) where
  A i j := coefficient ((rowIndex n L).symm i) ((variableIndex n L).symm j)
  b i := rowBound I ((rowIndex n L).symm i)
  c j := objective ((variableIndex n L).symm j)

def vector {n L : ℕ} (f : ℚ) (x : Arc n L → ℚ) :
    Fin (1+(n*n)*(L*(n*n))) → ℚ := fun j =>
  match (variableIndex n L).symm j with
  | .inl _ => f
  | .inr a => x a

private theorem sum_variables {n L : ℕ} (g : Variable n L → ℚ) :
    (∑ j : Fin (1+(n*n)*(L*(n*n))),g ((variableIndex n L).symm j)) =
      g (.inl 0)+∑ a : Arc n L,g (.inr a) := by
  rw [← Equiv.sum_comp (variableIndex n L)]
  simp

/-- The LP maximizes exactly the concurrent-flow value. -/
theorem objective_value {n L : ℕ} (I : RationalInstance n) (f : ℚ) (x : Arc n L → ℚ) :
    primalValue (program I L) (vector f x)=f := by
  simp only [primalValue,program,vector]
  change (∑ j,(fun v : Variable n L => objective v *
    (match v with | .inl _ => f | .inr a => x a)) ((variableIndex n L).symm j)) = _
  rw [sum_variables (n := n) (L := L) (fun v => objective v *
    (match v with | .inl _ => f | .inr a => x a))]
  simp [objective]

/-- The zero point is feasible at every layer budget, including zero. -/
theorem zero_feasible {n : ℕ} (I : RationalInstance n) (L : ℕ) :
    PrimalFeasible (program I L) (vector 0 (fun _ => 0)) := by
  have hz : vector (n := n) (L := L) 0 (fun _ => 0)=0 := by
    funext j
    simp only [vector]
    cases (variableIndex n L).symm j <;> rfl
  rw [hz]
  constructor
  · intro j; rfl
  · intro i
    simp only [rowValue,Pi.zero_apply,mul_zero,Finset.sum_const_zero,program]
    cases (rowIndex n L).symm i <;> simp only [rowBound] <;> positivity

end Lax455465Proofs.LayeredFlowLP
