import Lax455465Proofs.BoundaryData
import Lax455465Proofs.CutSweeps
import Lax455465Proofs.RegionRuntimeCorrespondence

namespace Lax455465Proofs.CutScoreData
open Lax455465.RationalEncoding MetricMatrix
open scoped BigOperators NNRat

def vertexFlags {n : ℕ} (S : Finset (Fin n)) : List ℚ≥0 := MaskedMassData.flags (ResidualData.mask S)
def arcFlags {n : ℕ} (S : Finset (Fin n)) : Matrix n := RamArcMask.matrix (some true) (ResidualData.mask S)
def mass {n : ℕ} (I : RationalInstance n) (S : Finset (Fin n)) : ℚ≥0 :=
  (RamMaskedSum.coefficients (List.ofFn I.weight) (vertexFlags S)).sum
def capacity {n : ℕ} (I : RationalInstance n) (S : Finset (Fin n)) : ℚ≥0 :=
  (RamMaskedSum.coefficients (values I.capacity) (values (arcFlags S))).sum
def otherMass {n : ℕ} (I : RationalInstance n) (S : Finset (Fin n)) : ℚ≥0 := RamRoundingInit.total I.weight-mass I S
def demand {n : ℕ} (I : RationalInstance n) (S : Finset (Fin n)) : ℚ≥0 := mass I S*otherMass I S
def ratio {n : ℕ} (I : RationalInstance n) (S : Finset (Fin n)) : ℚ≥0 := capacity I S/demand I S

theorem coe_mass {n : ℕ} (I : RationalInstance n) (S : Finset (Fin n)) : (mass I S : ℚ)=CutSweeps.massQ I S := by
  unfold mass vertexFlags
  rw [MaskedMassData.coe_sum]
  simp only [ResidualData.mask,decide_eq_true_eq,CutSweeps.massQ,←Finset.sum_filter]
  simp

theorem mass_add_complement {n : ℕ} (I : RationalInstance n) (S : Finset (Fin n)) :
    mass I S+mass I Sᶜ=RamRoundingInit.total I.weight := by
  apply NNRat.coe_injective
  rw [NNRat.coe_add,coe_mass,coe_mass,RegionRuntimeCorrespondence.coe_total]
  unfold CutSweeps.massQ LargeBallRounding.total
  exact Finset.sum_add_sum_compl S _

theorem otherMass_eq {n : ℕ} (I : RationalInstance n) (S : Finset (Fin n)) : otherMass I S=mass I Sᶜ := by
  rw [otherMass,←mass_add_complement I S,add_tsub_cancel_left]

theorem arc_condition {n : ℕ} (S : Finset (Fin n)) (u v : Fin n) : (arcFlags S u v).num=1 ↔ u∈S ∧ v∉S := by
  by_cases hu : u∈S <;> by_cases hv : v∈S <;>
    simp [arcFlags,RamArcMask.matrix,RamBooleanArithmetic.bit,RamBooleanArithmetic.flag,ResidualData.mask,hu,hv]

theorem coe_capacity {n : ℕ} (I : RationalInstance n) (S : Finset (Fin n)) : (capacity I S : ℚ)=CutSweeps.capacityQ I S := by
  unfold capacity
  rw [BoundaryData.masked_matrix]
  simp only [values,List.sum_ofFn]
  rw [←Equiv.sum_comp (DirectedFlowLP.edgeIndex n)]
  simp only [Equiv.symm_apply_apply,Fintype.sum_prod_type,NNRat.cast_sum]
  have hsum (T : Finset (Fin n)) (g : Fin n → ℚ) : (∑ v∈T,g v)=∑ v,if v∈T then g v else 0 := by
    have ht : Finset.univ.filter (fun v => v∈T)=T := by ext v; simp
    have h := Finset.sum_filter (s := Finset.univ) (p := fun v => v∈T) (f := g)
    rwa [ht] at h
  rw [CutSweeps.capacityQ,hsum S]
  simp_rw [hsum Sᶜ]
  simp only [Finset.mem_compl]
  apply Finset.sum_congr rfl
  intro u hu
  by_cases hus : u∈S
  · simp only [hus,if_true]
    apply Finset.sum_congr rfl
    intro v hv
    by_cases hvs : v∈S <;> simp [arc_condition,hus,hvs]
  · simp [arc_condition,hus]

theorem coe_demand {n : ℕ} (I : RationalInstance n) (S : Finset (Fin n)) :
    (demand I S : ℚ)=CutSweeps.massQ I S*CutSweeps.massQ I Sᶜ := by
  rw [demand,NNRat.coe_mul,otherMass_eq,coe_mass,coe_mass]

theorem coe_ratio {n : ℕ} (I : RationalInstance n) (S : Finset (Fin n)) : (ratio I S : ℚ)=CutSweeps.ratioQ I S := by
  rw [ratio,NNRat.coe_div,coe_capacity,coe_demand]
  rfl

theorem admissible_iff {n : ℕ} (I : RationalInstance n) (S : Finset (Fin n)) :
    CutSweeps.admissibleQ I S ↔ 0<(demand I S).num := by
  rw [CutSweeps.admissibleQ_iff_product_pos,←coe_demand]
  exact ⟨fun h => NNRat.num_pos.mpr (by exact_mod_cast h),fun h => by exact_mod_cast NNRat.num_pos.mp h⟩

end Lax455465Proofs.CutScoreData
