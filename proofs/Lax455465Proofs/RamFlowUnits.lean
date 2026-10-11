import Lax455465Proofs.RamFractionPrimitives

namespace Lax455465Proofs.RamFlowUnits

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamFractionPrimitives

def arcValue (commodity rowCommodity source target vertex : ℕ) : ℚ :=
  if commodity = rowCommodity then
    (if source = vertex then 1 else 0) - (if target = vertex then 1 else 0)
  else 0

def arc : Com := .ite (.eq (.var "lp.arcCommodity") (.var "lp.commodity"))
  (.ite (.eq (.var "lp.arcSource") (.var "lp.u"))
    (.ite (.eq (.var "lp.arcTarget") (.var "lp.u")) zero one)
    (.ite (.eq (.var "lp.arcTarget") (.var "lp.u")) negativeOne zero)) zero

theorem arc_spec (B a b u v z : ℕ) (h1 : 1 < B)
    (ha : a < B) (hb : b < B) (hu : u < B) (hv : v < B) (hz : z < B) :
    Spec B (fun σ => σ.vars "lp.arcCommodity" = a ∧ σ.vars "lp.commodity" = b ∧
      σ.vars "lp.arcSource" = u ∧ σ.vars "lp.arcTarget" = v ∧ σ.vars "lp.u" = z) arc
      (fun _ τ => FractionOutput (arcValue a b u v z) τ) 18 := by
  have hzero := zero_spec B h1
  have hone := one_spec B h1
  have hnegative := negativeOne_spec B h1
  rintro σ ⟨haσ,hbσ,huσ,hvσ,hzσ⟩
  run_vcg [hzero,hone,hnegative]
  all_goals simp_all [arcValue]

/-- Numerical capacity-row coefficient, with the flow-value column at zero. -/
def capacityValue (column arc row : ℕ) : ℚ :=
  if column = 0 then 0 else if arc = row then 1 else 0

def capacity : Com := .ite (.eq (.var "lp.j") (.lit 0)) zero
  (.ite (.eq (.var "lp.arc") (.var "lp.i")) one zero)

theorem capacity_spec (B column arcIndex row : ℕ) (h1 : 1 < B)
    (hc : column < B) (ha : arcIndex < B) (hr : row < B) :
    Spec B (fun σ => σ.vars "lp.j" = column ∧ σ.vars "lp.arc" = arcIndex ∧ σ.vars "lp.i" = row)
      capacity (fun _ τ => FractionOutput (capacityValue column arcIndex row) τ) 14 := by
  have hzero := zero_spec B h1
  have hone := one_spec B h1
  rintro σ ⟨hcol,harc,hrow⟩
  run_vcg [hzero,hone]
  all_goals simp_all [capacityValue]

def objective : Com := .ite (.eq (.var "lp.j") (.lit 0)) one zero

theorem objective_spec (B column : ℕ) (h1 : 1 < B) (hc : column < B) :
    Spec B (fun σ => σ.vars "lp.j" = column) objective
      (fun _ τ => FractionOutput (if column = 0 then 1 else 0) τ) 10 := by
  have hzero := zero_spec B h1
  have hone := one_spec B h1
  rintro σ hcol
  run_vcg [hzero,hone]
  all_goals simp_all

/-- Paired rows differ only by the sign of a coefficient. -/
def rowSign : Com := .ite (.eq (.var "lp.sign") (.lit 0)) .skip negate

theorem rowSign_spec (B flag : ℕ) (q : ℚ) (h1 : 1 < B) (hf : flag < B) :
    Spec B (fun σ => FractionOutput q σ ∧ σ.vars "lp.sign" = flag) rowSign
      (fun _ τ => FractionOutput (if flag = 0 then q else -q) τ) 8 := by
  have hneg := negate_spec B q h1
  rintro σ ⟨hvalue,hflag⟩
  run_vcg [hneg]
  all_goals simp_all

end Lax455465Proofs.RamFlowUnits
