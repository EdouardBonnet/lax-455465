import Lax455465Proofs.RamFlowUnits
import Lax455465Proofs.LayeredLpFlat

namespace Lax455465Proofs.RamLayeredUnits
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamFractionPrimitives

def half : Com := .seq (.assign "rat.s" (.lit 0))
  (.seq (.assign "rat.n" (.lit 1)) (.assign "rat.d" (.lit 2)))
def negativeHalf : Com := .seq (.assign "rat.s" (.lit 1))
  (.seq (.assign "rat.n" (.lit 1)) (.assign "rat.d" (.lit 2)))

theorem half_spec (B : ℕ) (h2 : 2 < B) :
    Spec B (fun _ => True) half (fun _ τ => FractionOutput (1/2) τ) 6 := by
  run_vcg
  all_goals simp [FractionOutput,fractionValue] <;> decide

theorem negativeHalf_spec (B : ℕ) (h2 : 2 < B) :
    Spec B (fun _ => True) negativeHalf (fun _ τ => FractionOutput (-1/2) τ) 6 := by
  have hrepr : (-1/2 : ℚ).num.natAbs=1 ∧ (-1/2 : ℚ).den=2 := by
    simpa [fractionValue] using fractionValue_num_den 1 1 2 (by decide)
  run_vcg
  all_goals simp [FractionOutput,fractionValue,hrepr.1,hrepr.2]

def arc : Com := .ite (.eq (.var "short.arcCommodity") (.var "short.rowCommodity"))
  (.ite (.eq (.var "short.arcLayer") (.var "short.rowLayer"))
    (.ite (.eq (.var "short.arcSource") (.var "short.rowVertex")) one zero)
    (.ite (.eq (.add (.var "short.arcLayer") (.lit 1)) (.var "short.rowLayer"))
      (.ite (.eq (.var "short.arcTarget") (.var "short.rowVertex")) negativeOne zero) zero)) zero

theorem arc_spec (B ac rc k j u v z : ℕ) (h1 : 1 < B)
    (hac : ac < B) (hrc : rc < B) (hk : k+1 < B) (hj : j < B)
    (hu : u < B) (hv : v < B) (hz : z < B) :
    Spec B (fun σ => σ.vars "short.arcCommodity"=ac ∧ σ.vars "short.rowCommodity"=rc ∧
      σ.vars "short.arcLayer"=k ∧ σ.vars "short.rowLayer"=j ∧
      σ.vars "short.arcSource"=u ∧ σ.vars "short.arcTarget"=v ∧ σ.vars "short.rowVertex"=z)
      arc (fun _ τ => FractionOutput (LayeredLpFlat.incidenceValue ac rc k j u v z) τ) 28 := by
  have hzero := zero_spec B h1
  have hone := one_spec B h1
  have hneg := negativeOne_spec B h1
  have hk' : k < B := by omega
  rintro σ ⟨hσac,hσrc,hσk,hσj,hσu,hσv,hσz⟩
  run_vcg [hzero,hone,hneg]
  all_goals simp_all [LayeredLpFlat.incidenceValue]
  all_goals omega

def demand : Com := .ite (.eq (.var "short.s") (.var "short.t")) zero
  (.ite (.eq (.var "short.rowLayer") (.lit 0))
    (.ite (.eq (.var "short.rowVertex") (.var "short.s")) negativeHalf
      (.ite (.eq (.var "short.rowLayer") (.var "short.layer"))
        (.ite (.eq (.var "short.rowVertex") (.var "short.t")) half zero) zero))
    (.ite (.eq (.var "short.rowLayer") (.var "short.layer"))
      (.ite (.eq (.var "short.rowVertex") (.var "short.t")) half zero) zero))

def demandValue (L s t j u : ℕ) : ℚ :=
  if s=t then 0 else -((if j=0 ∧ u=s then 1 else 0)-(if j=L ∧ u=t then 1 else 0))/2

theorem demand_spec (B L s t j u : ℕ) (h2 : 2 < B) (hL : L < B)
    (hs : s < B) (ht : t < B) (hj : j < B) (hu : u < B) :
    Spec B (fun σ => σ.vars "short.layer"=L ∧ σ.vars "short.s"=s ∧ σ.vars "short.t"=t ∧
      σ.vars "short.rowLayer"=j ∧ σ.vars "short.rowVertex"=u) demand
      (fun _ τ => FractionOutput (demandValue L s t j u) τ) 30 := by
  have hzero := zero_spec B (by omega)
  have hhalf := half_spec B h2
  have hnegative := negativeHalf_spec B h2
  rintro σ ⟨hσL,hσs,hσt,hσj,hσu⟩
  run_vcg [hzero,hhalf,hnegative]
  all_goals simp_all [demandValue]

def capacity : Com := .ite (.eq (.var "lp.j") (.lit 0)) zero
  (.ite (.eq (.var "short.capSource") (.var "short.capTarget")) zero
    (.ite (.eq (.var "short.arcSource") (.var "short.capSource"))
      (.ite (.eq (.var "short.arcTarget") (.var "short.capTarget")) one zero)
      (.ite (.eq (.var "short.arcSource") (.var "short.capTarget"))
        (.ite (.eq (.var "short.arcTarget") (.var "short.capSource")) one zero) zero)))

def capacityValue (j a b u v : ℕ) : ℚ :=
  if j=0 then 0 else if a=b then 0 else
    (if u=a ∧ v=b then 1 else 0)+(if u=b ∧ v=a then 1 else 0)

theorem capacity_spec (B j a b u v : ℕ) (h1 : 1 < B)
    (hj : j < B) (ha : a < B) (hb : b < B) (hu : u < B) (hv : v < B) :
    Spec B (fun σ => σ.vars "lp.j"=j ∧ σ.vars "short.capSource"=a ∧ σ.vars "short.capTarget"=b ∧
      σ.vars "short.arcSource"=u ∧ σ.vars "short.arcTarget"=v) capacity
      (fun _ τ => FractionOutput (capacityValue j a b u v) τ) 30 := by
  have hzero := zero_spec B h1
  have hone := one_spec B h1
  rintro σ ⟨hσj,hσa,hσb,hσu,hσv⟩
  run_vcg [hzero,hone]
  all_goals simp_all [capacityValue]

def rowSign : Com := .ite (.eq (.var "short.rowSign") (.lit 0)) .skip negate

theorem rowSign_spec (B flag : ℕ) (q : ℚ) (h1 : 1 < B) (hf : flag < B) :
    Spec B (fun σ => FractionOutput q σ ∧ σ.vars "short.rowSign"=flag) rowSign
      (fun _ τ => FractionOutput (if flag=0 then q else -q) τ) 8 := by
  have hneg := negate_spec B q h1
  rintro σ ⟨hvalue,hflag⟩
  run_vcg [hneg]
  all_goals simp_all

end Lax455465Proofs.RamLayeredUnits
