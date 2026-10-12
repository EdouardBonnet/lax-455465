import Lax455465Proofs.RamScalarDifference
import Lax455465Proofs.RamScalarReciprocal
import Lax455465Proofs.RamCutMeasures

namespace Lax455465Proofs.RamCutRatio
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar RamRegionContext
open Lax455465.RationalEncoding CutScoreData
open scoped NNRat

structure Input {n : ℕ} (I : RationalInstance n) (S : Finset (Fin n)) (σ : Env) : Prop where
  totalData : Stored "round.total" (RamRoundingInit.total I.weight) σ
  capacityData : Stored "cut.capacity" (capacity I S) σ
  massData : Stored "cut.mass" (mass I S) σ

def valid : Com := .ite (.eq (.var "cut.demand.n") (.lit 0))
  (.assign "cut.valid" (.lit 0)) (.assign "cut.valid" (.lit 1))
def command : Com := .seq (RamScalarDifference.command "round.total" "cut.mass" "cut.other")
  (.seq (RamScalarProduct.command "cut.mass" "cut.other" "cut.demand")
    (.seq (RamScalarReciprocal.command "cut.demand" "cut.inverseDemand")
      (.seq (RamScalarProduct.command "cut.capacity" "cut.inverseDemand" "cut.ratio") valid)))

set_option maxHeartbeats 2400000 in
/-- Compute the product demand, exact sparsity ratio, and positive-demand
flag from the previously measured shore. Zero demand is detected explicitly
before the minimum-ratio cut selector uses this score. -/
theorem command_spec (B M : ℕ) {n : ℕ} (I : RationalInstance n) (S : Finset (Fin n)) (hM : 1≤M)
    (hb : CutScoreHeight.Bounds I S M) (hB : 2*M^2+3<B) :
    Spec B (Input I S) command (fun _ τ => Input I S τ ∧ Stored "cut.other" (otherMass I S) τ ∧
      Stored "cut.demand" (demand I S) τ ∧ Stored "cut.ratio" (ratio I S) τ ∧
      τ.vars "cut.valid"=if CutSweeps.admissibleQ I S then 1 else 0) (144*(M^2).size+416) := by
  have hsize {a b : ℚ≥0} (ha : LpInputSize.Height M (a : ℚ)) (hb : LpInputSize.Height M (b : ℚ)) :
      (a.den*b.den).size≤(M^2).size := Nat.size_le_size (by nlinarith [Nat.mul_le_mul (den_bound ha) (den_bound hb)])
  have hnumsize : (demand I S).num.size≤(M^2).size := Nat.size_le_size (by nlinarith [num_bound hb.demandBound])
  have h2 : 2<B := by nlinarith
  rintro σ hσ
  obtain ⟨σ1,r1,p1⟩ := RamScalarDifference.command_spec B M (RamRoundingInit.total I.weight) (mass I S)
    "round.total" "cut.mass" "cut.other" hB hb.totalBound hb.massBound hb.otherBound
    (by decide) (by decide) (by decide) (by decide) σ ⟨hσ.totalData,hσ.massData⟩
  obtain ⟨σ2,r2,p2⟩ := RamScalarProduct.command_spec B M (mass I S) (otherMass I S)
    "cut.mass" "cut.other" "cut.demand" hB (num_bound hb.massBound) (den_bound hb.massBound)
    (num_bound hb.otherBound) (den_bound hb.otherBound) (by decide) (by decide) (by decide) (by decide) σ1
    ⟨RamRoundingConstants.storedFrame r1 hσ.massData (by decide) (by decide),p1⟩
  obtain ⟨σ3,r3,p3⟩ := RamScalarReciprocal.command_spec B M (demand I S) "cut.demand" "cut.inverseDemand" hM (by nlinarith) hb.demandBound
    (by decide) (by decide) σ2 p2
  have r123 := r1.seq (r2.seq r3)
  obtain ⟨σ4,r4,p4⟩ := RamScalarProduct.command_spec B M (capacity I S) (demand I S)⁻¹
    "cut.capacity" "cut.inverseDemand" "cut.ratio" hB (num_bound hb.cutCapacityBound) (den_bound hb.cutCapacityBound)
    (num_bound hb.inverseBound) (den_bound hb.inverseBound) (by decide) (by decide) (by decide) (by decide) σ3
    ⟨RamRoundingConstants.storedFrame r123 hσ.capacityData (by decide) (by decide),p3⟩
  have hd : σ4.vars "cut.demand.n"=(demand I S).num :=
    ((r3.seq r4).frame_var _ (by decide)).trans p2.1
  have hdB : σ4.vars "cut.demand.n"<B := by rw [hd]; exact (num_bound hb.demandBound).trans_lt (by nlinarith)
  have hv : ∃ τ, Run B valid σ4 τ 6 ∧ τ.vars "cut.valid"=if CutSweeps.admissibleQ I S then 1 else 0 := by
    by_cases hz : (demand I S).num=0
    · have hc : (Cond.eq (.var "cut.demand.n") (.lit 0)).evalB B σ4=some true := by
        rw [evalB_condEq (evalB_var hdB) (evalB_lit (by omega)),hd,hz]
        rfl
      have rr : Run B (.assign "cut.valid" (.lit 0)) σ4 (σ4.setVar "cut.valid" 0) 2 := Run.assign (evalB_lit (by omega))
      refine ⟨σ4.setVar "cut.valid" 0,Run.ite_true (d := .assign "cut.valid" (.lit 1)) hc rr,?_⟩
      simp only [vars_setVar,if_true,admissible_iff,hz,lt_self_iff_false,if_false]
    · have hc : (Cond.eq (.var "cut.demand.n") (.lit 0)).evalB B σ4=some false := by
        rw [evalB_condEq (evalB_var hdB) (evalB_lit (by omega)),hd]
        simp [hz]
      have rr : Run B (.assign "cut.valid" (.lit 1)) σ4 (σ4.setVar "cut.valid" 1) 2 := Run.assign (evalB_lit (by omega))
      refine ⟨σ4.setVar "cut.valid" 1,Run.ite_false (c := .assign "cut.valid" (.lit 0)) hc rr,?_⟩
      simp only [vars_setVar,if_true,admissible_iff,Nat.pos_of_ne_zero hz,if_true]
  obtain ⟨τ,r5,p5⟩ := hv
  have rr := r1.seq (r2.seq (r3.seq (r4.seq r5)))
  refine ⟨τ,rr.mono ?_,?_,?_,?_,?_,p5⟩
  · have hs1 := hsize hb.totalBound hb.massBound
    have hs2 := hsize hb.massBound hb.otherBound
    have hs4 := hsize hb.cutCapacityBound hb.inverseBound
    nlinarith
  · exact ⟨RamRoundingConstants.storedFrame rr hσ.totalData (by decide) (by decide),
      RamRoundingConstants.storedFrame rr hσ.capacityData (by decide) (by decide),
      RamRoundingConstants.storedFrame rr hσ.massData (by decide) (by decide)⟩
  · exact RamRoundingConstants.storedFrame (r2.seq (r3.seq (r4.seq r5))) p1 (by decide) (by decide)
  · exact RamRoundingConstants.storedFrame (r3.seq (r4.seq r5)) p2 (by decide) (by decide)
  · have hp := RamRoundingConstants.storedFrame r5 p4 (by decide) (by decide)
    simpa only [ratio,div_eq_mul_inv] using hp

end Lax455465Proofs.RamCutRatio
