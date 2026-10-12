import Lax455465Proofs.RoundingConstantHeight
import Lax455465Proofs.RamScalarReciprocal
import Lax455465Proofs.RamScalarProduct
import Lax455465Proofs.RamNatScalar

namespace Lax455465Proofs.RamRoundingConstants
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamUnsignedScalar RamRegionContext RoundingConstants
open scoped NNRat

def unitCost (M : ℕ) : ℕ := 36*(M^2).size+100

theorem storedFrame {B K : ℕ} {cmd : Com} {σ τ : Env} (rr : Run B cmd σ τ K)
    {name : String} {q : ℚ≥0} (h : Stored name q σ)
    (hn : name++".n"∉cmd.wvars) (hd : name++".d"∉cmd.wvars) : Stored name q τ := by
  simpa only [Stored,rr.frame_var (name++".n") hn,rr.frame_var (name++".d") hd] using h

theorem product_spec (B M : ℕ) (a b : ℚ≥0) (leftName rightName target : String)
    (hM : 1≤M) (hB : 2*M^2+3<B) (ha : LpInputSize.Height M (a : ℚ)) (hb : LpInputSize.Height M (b : ℚ))
    (hl : leftName++".n"≠"rat.s" ∧ leftName++".d"≠"rat.s" ∧ leftName++".d"≠"rat.n")
    (hr : rightName++".n"≠"rat.s" ∧ rightName++".d"≠"rat.s" ∧ rightName++".d"≠"rat.n")
    (hf : rightName++".n"∉(Com.seq (load leftName) (RamUnsignedArithmetic.copy "left")).wvars ∧
      rightName++".d"∉(Com.seq (load leftName) (RamUnsignedArithmetic.copy "left")).wvars)
    (ht : target++".n"≠"rat.d") :
    Spec B (fun σ => Stored leftName a σ ∧ Stored rightName b σ)
      (RamScalarProduct.command leftName rightName target) (fun _ τ => Stored target (a*b) τ) (unitCost M) := by
  rintro σ hσ
  obtain ⟨τ,rr,pr⟩ := RamScalarProduct.command_spec B M a b leftName rightName target hB
    (num_bound ha) (den_bound ha) (num_bound hb) (den_bound hb) hl hr hf ht σ hσ
  have hs : (a.den*b.den).size≤(M^2).size := Nat.size_le_size (by nlinarith [Nat.mul_le_mul (den_bound ha) (den_bound hb)])
  exact ⟨τ,rr.mono (by dsimp [unitCost]; omega),pr⟩

theorem reciprocal_spec (B M : ℕ) (q : ℚ≥0) (source target : String)
    (hM : 1≤M) (hB : 2*M^2+3<B) (hq : LpInputSize.Height M (q : ℚ))
    (hs : source++".n"≠"rat.s" ∧ source++".d"≠"rat.s" ∧ source++".d"≠"rat.n")
    (ht : target++".n"≠"rat.d") :
    Spec B (Stored source q) (RamScalarReciprocal.command source target)
      (fun _ τ => Stored target q⁻¹ τ) (unitCost M) := by
  rintro σ hσ
  obtain ⟨τ,rr,pr⟩ := RamScalarReciprocal.command_spec B M q source target hM (by nlinarith) hq hs ht σ hσ
  have hsize : q.num.size≤(M^2).size := Nat.size_le_size (by nlinarith [num_bound hq])
  exact ⟨τ,rr.mono (by dsimp [unitCost]; omega),pr⟩

structure Input (cost total : ℚ≥0) (p : ℕ) (σ : Env) : Prop where
  costData : Stored "round.cost" cost σ
  totalData : Stored "round.total" total σ
  supportValue : σ.vars "round.support"=p
  stepsValue : σ.vars "round.steps"=RegionBudget.steps p

def stage1 : Com := RamNatScalar.command "round.support" "round.supportRat"
def stage2 : Com := RamScalarReciprocal.command "round.supportRat" "round.inverseSupport"
def stage3 : Com := RamScalarProduct.command "round.cost" "round.inverseSupport" "round.seed"
def stage4 : Com := RamScalarProduct.command "round.total" "round.total" "round.square"
def stage5 : Com := Com.seq (.assign "round.four.n" (.lit 4)) (.assign "round.four.d" (.lit 1))
def stage6 : Com := RamScalarProduct.command "round.four" "round.square" "round.denominator"
def stage7 : Com := RamScalarReciprocal.command "round.denominator" "round.delta"
def stage8 : Com := RamNatScalar.command "round.steps" "round.stepsRat"
def stage9 : Com := RamScalarReciprocal.command "round.delta" "round.inverseDelta"
def stage10 : Com := RamScalarProduct.command "round.stepsRat" "round.inverseDelta" "round.slope"
def stage11 : Com := RamScalarReciprocal.command "round.stepsRat" "round.inverseSteps"
def stage12 : Com := RamScalarProduct.command "round.delta" "round.inverseSteps" "round.gridStep"

def command : Com := .seq stage1 (.seq stage2 (.seq stage3 (.seq stage4 (.seq stage5 (.seq stage6 (.seq stage7 (.seq stage8 (.seq stage9 (.seq stage10 (.seq stage11 (.seq stage12 (.skip))))))))))))

set_option maxHeartbeats 2400000 in
/-- Compute every region-growth constant by a fixed sequence of exact native
rational operations, using only the stored input mass, support and metric
cost. The height parameter bounds execution; it is not runtime advice. -/
theorem command_spec (B M : ℕ) (cost total : ℚ≥0) (p : ℕ)
    (hb : RoundingConstantHeight.Bounds cost total p M) (hM : 4≤M) (hB : 2*M^2+3<B) :
    Spec B (Input cost total p) command (fun _ τ => Input cost total p τ ∧
      Stored "round.seed" (seed cost p) τ ∧ Stored "round.delta" (delta total) τ ∧
      Stored "round.slope" (beta total p) τ ∧ Stored "round.gridStep" (gridStep total p) τ)
      (12*unitCost M+1) := by
  have hM1 : 1≤M := by omega
  have hMB : M<B := by nlinarith
  have hp : p<B := by
    have h := num_bound hb.supportBound
    simpa only [NNRat.num_natCast] using h.trans_lt hMB
  have hk : RegionBudget.steps p<B := by
    have h := num_bound hb.stepsBound
    simpa only [NNRat.num_natCast] using h.trans_lt hMB
  have hpnInv := inverse_height hM1 hb.supportBound
  have hkInv := inverse_height hM1 hb.stepsBound
  have hdelta : LpInputSize.Height M (((4*(total*total))⁻¹ : ℚ≥0) : ℚ) := by simpa only [delta,pow_two] using hb.deltaBound
  have hdeltaInv := inverse_height hM1 hdelta
  rintro σ hσ
  obtain ⟨σ1,raw1,p1⟩ := RamNatScalar.command_spec B (p) "round.support" "round.supportRat" hp (by omega) σ (hσ.supportValue)
  have r1 : Run B stage1 σ σ1 (unitCost M) := raw1.mono (by dsimp [unitCost]; omega)
  obtain ⟨σ2,r2,p2⟩ := reciprocal_spec B M ((p : ℚ≥0)) "round.supportRat" "round.inverseSupport" hM1 hB hb.supportBound (by decide) (by decide) σ1 p1
  obtain ⟨σ3,r3,p3⟩ := product_spec B M (cost) ((p : ℚ≥0)⁻¹) "round.cost" "round.inverseSupport" "round.seed" hM1 hB hb.costBound hpnInv (by decide) (by decide) (by decide) (by decide) σ2
    ⟨(storedFrame (r1.seq (r2)) hσ.costData (by decide) (by decide)),p2⟩
  obtain ⟨σ4,r4,p4⟩ := product_spec B M (total) (total) "round.total" "round.total" "round.square" hM1 hB hb.totalBound hb.totalBound (by decide) (by decide) (by decide) (by decide) σ3
    ⟨(storedFrame (r1.seq (r2.seq (r3))) hσ.totalData (by decide) (by decide)),(storedFrame (r1.seq (r2.seq (r3))) hσ.totalData (by decide) (by decide))⟩
  have hfour : Spec B (fun _ => True) stage5 (fun _ τ => Stored "round.four" 4 τ) 4 := by
    run_vcg
    all_goals simp [Stored]
  obtain ⟨σ5,raw5,p5⟩ := hfour σ4 True.intro
  have r5 : Run B stage5 σ4 σ5 (unitCost M) := raw5.mono (by dsimp [unitCost]; omega)
  obtain ⟨σ6,r6,p6⟩ := product_spec B M ((4 : ℚ≥0)) (total*total) "round.four" "round.square" "round.denominator" hM1 hB hb.fourBound hb.squareBound (by decide) (by decide) (by decide) (by decide) σ5
    ⟨p5,(storedFrame (r5) p4 (by decide) (by decide))⟩
  obtain ⟨σ7,r7,p7⟩ := reciprocal_spec B M (4*(total*total)) "round.denominator" "round.delta" hM1 hB hb.denominatorBound (by decide) (by decide) σ6 p6
  obtain ⟨σ8,raw8,p8⟩ := RamNatScalar.command_spec B (RegionBudget.steps p) "round.steps" "round.stepsRat" hk (by omega) σ7 (((r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq (r7))))))).frame_var "round.steps" (by decide)).trans hσ.stepsValue)
  have r8 : Run B stage8 σ7 σ8 (unitCost M) := raw8.mono (by dsimp [unitCost]; omega)
  obtain ⟨σ9,r9,p9⟩ := reciprocal_spec B M ((4*(total*total))⁻¹) "round.delta" "round.inverseDelta" hM1 hB hdelta (by decide) (by decide) σ8 (storedFrame (r8) p7 (by decide) (by decide))
  obtain ⟨σ10,r10,p10⟩ := product_spec B M ((RegionBudget.steps p : ℚ≥0)) (((4*(total*total))⁻¹)⁻¹) "round.stepsRat" "round.inverseDelta" "round.slope" hM1 hB hb.stepsBound hdeltaInv (by decide) (by decide) (by decide) (by decide) σ9
    ⟨(storedFrame (r9) p8 (by decide) (by decide)),p9⟩
  obtain ⟨σ11,r11,p11⟩ := reciprocal_spec B M ((RegionBudget.steps p : ℚ≥0)) "round.stepsRat" "round.inverseSteps" hM1 hB hb.stepsBound (by decide) (by decide) σ10 (storedFrame (r9.seq (r10)) p8 (by decide) (by decide))
  obtain ⟨σ12,r12,p12⟩ := product_spec B M ((4*(total*total))⁻¹) ((RegionBudget.steps p : ℚ≥0)⁻¹) "round.delta" "round.inverseSteps" "round.gridStep" hM1 hB hdelta hkInv (by decide) (by decide) (by decide) (by decide) σ11
    ⟨(storedFrame (r8.seq (r9.seq (r10.seq (r11)))) p7 (by decide) (by decide)),p11⟩
  have rr := r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq (r7.seq (r8.seq (r9.seq (r10.seq (r11.seq (r12.seq Run.skip)))))))))))
  refine ⟨σ12,rr.mono (by omega),?_,?_,?_,?_,?_⟩
  · refine ⟨storedFrame rr hσ.costData (by decide) (by decide),storedFrame rr hσ.totalData (by decide) (by decide),
      (rr.frame_var "round.support" (by decide)).trans hσ.supportValue,(rr.frame_var "round.steps" (by decide)).trans hσ.stepsValue⟩
  · simpa only [seed,div_eq_mul_inv] using (storedFrame (r4.seq (r5.seq (r6.seq (r7.seq (r8.seq (r9.seq (r10.seq (r11.seq (r12))))))))) p3 (by decide) (by decide))
  · simpa only [delta,pow_two] using (storedFrame (r8.seq (r9.seq (r10.seq (r11.seq (r12))))) p7 (by decide) (by decide))
  · simpa only [beta,delta,pow_two,div_eq_mul_inv] using (storedFrame (r11.seq (r12)) p10 (by decide) (by decide))
  · simpa only [gridStep,delta,pow_two,div_eq_mul_inv] using p12

end Lax455465Proofs.RamRoundingConstants
