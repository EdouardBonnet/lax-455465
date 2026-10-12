import Lax455465Proofs.PositivePairData
import Lax455465Proofs.RamRootDistances
import Lax455465Proofs.RamPotentialSweep
import Lax455465Proofs.RamSetPotential
import Lax455465Proofs.PotentialCandidates

set_option maxRecDepth 8192
namespace Lax455465Proofs.RamZeroCut
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar RamRegionContext
open Lax455465.RationalEncoding DirectedFlowLP
open scoped BigOperators NNRat

structure Input {n : ℕ} (I : RationalInstance n) (d : MetricMatrix.Matrix n) (σ : Env) : Prop where
  nValue : σ.vars "metric.n"=n
  n2Value : σ.vars "metric.n2"=n*n
  weights : Prefix (RamUnsignedBuffer.encode (List.ofFn I.weight)) "flow.weights" σ
  capacities : Prefix (RamUnsignedBuffer.encode (MetricMatrix.values I.capacity)) "flow.capacities" σ
  distances : Prefix (RamUnsignedBuffer.encode (MetricMatrix.values d)) "metric.old" σ
  total : Stored "round.total" (RamRoundingInit.total I.weight) σ

def names : List String := ["metric.n","metric.n2","round.total.n","round.total.d"]
def arrays : List String := ["flow.weights","flow.capacities","metric.old"]
def Room (n : ℕ) (σ : Env) : Prop :=
  (∀ a∈["region.out","cut.potential","cut.flags"],2*n<(σ.arrs a).length) ∧
    2*(n*n)<(σ.arrs "cut.crossing").length

theorem Input.frame {B K : ℕ} {cmd : Com} {σ τ : Env} (rr : Run B cmd σ τ K)
    {n : ℕ} {I : RationalInstance n} {d : MetricMatrix.Matrix n} (h : Input I d σ)
    (hx : ∀ x∈names,x∉cmd.wvars) (ha : ∀ a∈RamZeroCut.arrays,a∉cmd.warrs) : Input I d τ := by
  exact ⟨(rr.frame_var _ (hx _ (by simp [names]))).trans h.nValue,
    (rr.frame_var _ (hx _ (by simp [names]))).trans h.n2Value,
    by simpa only [Prefix,rr.frame_arr "flow.weights" (ha _ (by simp [RamZeroCut.arrays]))] using h.weights,
    by simpa only [Prefix,rr.frame_arr "flow.capacities" (ha _ (by simp [RamZeroCut.arrays]))] using h.capacities,
    by simpa only [Prefix,rr.frame_arr "metric.old" (ha _ (by simp [RamZeroCut.arrays]))] using h.distances,
    RamRoundingConstants.storedFrame rr h.total (hx _ (by simp [names])) (hx _ (by simp [names]))⟩

theorem Room.frame {B K : ℕ} {cmd : Com} {σ τ : Env} (rr : Run B cmd σ τ K)
    {n : ℕ} (h : Room n σ) : Room n τ := by
  exact ⟨fun a ha => by rw [RamFrames.run_array_length rr]; exact h.1 a ha,
    by rw [RamFrames.run_array_length rr]; exact h.2⟩

def prepare : Com := .seq RamPositivePair.command
  (.seq (.assign "region.root" (.div (.var "find.result") (.var "metric.n")))
    (.seq (RamRootDistances.command true)
      (.seq (.assign "copy.count" (.mul (.lit 2) (.var "metric.n")))
        (.seq (RamArrayCopy.command "region.out" "cut.potential" "copy.count")
          (.seq (.assign "cut.reversed" (.lit 0)) (.assign "cut.count" (.var "metric.n")))))))
def prepareCost (n : ℕ) : ℕ := 98*(n*n)+66*n+38
def command : Com := .seq prepare RamPotentialSweep.command
def cost (n M : ℕ) : ℕ := prepareCost n+RamPotentialSweep.cost n M

set_option maxHeartbeats 4800000 in
theorem prepare_spec (B M : ℕ) {n : ℕ} (I : RationalInstance n) (d : MetricMatrix.Matrix n)
    (hMB : M<B) (h2 : 2<B) (hindex : 2*(n*n)+2<B) (hvertex : 2*n+2<B)
    (hw : ∀ v,LpInputSize.Height M (I.weight v : ℚ)) (hd : ∀ u v,LpInputSize.Height M (d u v : ℚ))
    (hsep : 1≤LargeBallRounding.distanceSeparation I (MetricMatrix.rational d)) :
    Spec B (fun σ => Input I d σ ∧ Room n σ) prepare
      (fun _ τ => Input I d τ ∧ ∃ u v,
        0<ZeroCostRounding.pairTerm I (MetricMatrix.rational d) (u,v) ∧
        τ.vars "cut.count"=n ∧ τ.vars "cut.reversed"=0 ∧
        Prefix (RamUnsignedBuffer.encode (List.ofFn (d u))) "cut.potential" τ) (prepareCost n) := by
  obtain ⟨u,v,hfirst,hpair⟩ := PositivePairData.first_correct I d hsep
  let edge := (edgeIndex n (u,v)).val
  have heB : edge<B := (edgeIndex n (u,v)).isLt.trans (by omega)
  have huB : u.val<B := u.isLt.trans (by omega)
  rintro σ ⟨hσ,hroom⟩
  obtain ⟨σ1,r1,p1⟩ := RamPositivePair.command_spec B M I d hMB h2 hindex hvertex hw hd σ
    ⟨hσ.nValue,hσ.n2Value,hσ.weights,hσ.distances⟩
  have h1 := Input.frame r1 hσ (by dsimp [names]; decide) (by dsimp [RamZeroCut.arrays]; decide)
  have hm : RamFind.Matches (some edge) σ1 := by simpa only [hfirst,edge] using p1.2
  let σ2 := σ1.setVar "region.root" u.val
  have r2 : Run B (.assign "region.root" (.div (.var "find.result") (.var "metric.n"))) σ1 σ2 4 := by
    have hdiv : edge/n=u.val := FlowLpIndices.edge_div u v
    have hh := evalB_bin (op := .div)
      (by rw [evalB_var_iff]; exact ⟨hm.2.symm,hm.2 ▸ heB⟩)
      (by rw [evalB_var_iff]; exact ⟨h1.nValue.symm,h1.nValue ▸ (by omega : n<B)⟩)
      (by change edge/n<B; rw [hdiv]; exact huB)
    simpa only [σ2,Bop.apply,hdiv,Expr.size,Nat.reduceAdd] using (Run.assign hh : Run B _ _ _ 4)
  have h2σ := Input.frame r2 h1 (by dsimp [names]; decide) (by dsimp [RamZeroCut.arrays]; decide)
  obtain ⟨σ3,r3,p3⟩ := RamRootDistances.command_spec B M true u d hMB (by omega) (by omega) hindex
    (fun u v => num_bound (hd u v)) (fun u v => den_bound (hd u v)) σ2
    ⟨⟨h2σ.nValue,by simp [σ2],h2σ.distances⟩,((hroom.frame (r1.seq r2)).1 _ (by simp [RamRootDistances.array]))⟩
  have h3 := Input.frame r3 h2σ (by dsimp [names]; decide) (by dsimp [RamZeroCut.arrays]; decide)
  let σ4 := σ3.setVar "copy.count" (2*n)
  have r4 : Run B (.assign "copy.count" (.mul (.lit 2) (.var "metric.n"))) σ3 σ4 4 :=
    Run.assign (evalB_bin (op := .mul) (evalB_lit h2)
      (by rw [evalB_var_iff]; exact ⟨h3.nValue.symm,h3.nValue ▸ (by omega : n<B)⟩)
      (by dsimp [Bop.apply]; omega))
  let xs := RamUnsignedBuffer.encode (List.ofFn (d u))
  have hxlen : xs.length=2*n := by simp [xs]
  have hwords : ∀ x∈xs,x<B := RamSetPotential.encoded_bound B M (List.ofFn (d u)) hMB
    (by intro q hq; obtain ⟨v,rfl⟩ := List.mem_ofFn.mp hq; exact hd u v)
  have rr4 := r1.seq (r2.seq (r3.seq r4))
  obtain ⟨σ5,r5,p5⟩ := RamArrayCopy.command_spec B xs "region.out" "cut.potential" "copy.count" (by omega)
    (by rw [hxlen]; omega) hwords (by decide) (by decide) σ4
    ⟨by simpa only [Prefix,σ4,arrs_setVar,RamRootDistances.vector,RamRootDistances.array,if_true] using p3.2,
      by simp [σ4,hxlen],by rw [hxlen]; exact ((hroom.frame rr4).1 _ (by simp)).le⟩
  let σ6 := σ5.setVar "cut.reversed" 0
  have r6 : Run B (.assign "cut.reversed" (.lit 0)) σ5 σ6 2 := Run.assign (evalB_lit (by omega))
  have h5 := Input.frame (rr4.seq r5) hσ (by dsimp [names]; decide) (by dsimp [RamZeroCut.arrays]; decide)
  let τ := σ6.setVar "cut.count" n
  have hn6 : σ6.vars "metric.n"=n := by simpa [σ6] using h5.nValue
  have r7 : Run B (.assign "cut.count" (.var "metric.n")) σ6 τ 2 :=
    Run.assign (by rw [evalB_var_iff]; exact ⟨hn6.symm,hn6 ▸ (by omega : n<B)⟩)
  have rr := r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq r7)))))
  exact ⟨τ,rr.mono (by rw [hxlen]; dsimp [prepareCost]; omega),
    Input.frame rr hσ (by dsimp [names]; decide) (by dsimp [RamZeroCut.arrays]; decide),u,v,hpair,
    by simp [τ],by simp [τ,σ6],p5.2⟩

set_option maxHeartbeats 3200000 in
/-- At zero metric cost, the actual pair search, distance-vector extraction,
and threshold sweep return an admissible cut with zero capacity ratio. -/
theorem command_spec (B M : ℕ) {n : ℕ} (I : RationalInstance n) (d : MetricMatrix.Matrix n)
    (hM : 1≤M) (hB : 2*M^2+3<B) (hindex : 2*(n*n)+2<B) (hvertex : 2*n+2<B)
    (hw : ∀ v,LpInputSize.Height M (I.weight v : ℚ)) (hd : ∀ u v,LpInputSize.Height M (d u v : ℚ))
    (hcuts : ∀ S,CutScoreHeight.Bounds I S M) (hdiag : ∀ v,d v v=0)
    (htri : ∀ u v w,(d u w : ℚ)≤(d u v : ℚ)+(d v w : ℚ))
    (hsep : 1≤LargeBallRounding.distanceSeparation I (MetricMatrix.rational d))
    (hzero : (∑ u,∑ v,(I.capacity u v : ℚ)*(d u v : ℚ))=0) :
    Spec B (fun σ => Input I d σ ∧ Room n σ) command
      (fun _ τ => ∃ S : Finset (Fin n),CutSweeps.admissibleQ I S ∧ CutSweeps.ratioQ I S≤0 ∧
        Prefix (RamUnsignedBuffer.encode (CutScoreData.vertexFlags S)) "cut.flags" τ) (cost n M) := by
  rintro σ ⟨hσ,hroom⟩
  obtain ⟨ν,rp,hν,u,v,hpair,hcount,hrev,hpotential⟩ := prepare_spec B M I d (by nlinarith) (by nlinarith)
    hindex hvertex hw hd hsep σ ⟨hσ,hroom⟩
  have hpositive := ZeroCostRounding.potential_separation I (MetricMatrix.rational d) (u,v)
    (fun _ _ => NNRat.coe_nonneg _) (by intro v; simp [MetricMatrix.rational,hdiag]) hpair
  obtain ⟨S,hS,hvalid,hratio⟩ := PotentialLayers.round_spec I (MetricMatrix.rational d u) hpositive
  have hzeroRatio : CutSweeps.ratioQ I S≤0 := hratio.trans (by
    have hc := PotentialLayers.edgeCost_le I (MetricMatrix.rational d u) (MetricMatrix.rational d)
      (fun _ _ => NNRat.coe_nonneg _) (by intro v w; have ht := htri u v w; dsimp [MetricMatrix.rational]; linarith)
    dsimp only [MetricMatrix.rational] at hc
    rw [hzero] at hc
    exact div_nonpos_of_nonpos_of_nonneg hc hpositive.le)
  have hSmem : S∈CutSweeps.candidates (ThresholdCutData.potential false (d u)) :=
    PotentialCandidates.round_mem I _ S hS
  obtain ⟨j,hj,hjn,hjvalid,hjratio⟩ := RamPotentialSweep.selected_le I (d u) false S hSmem hvalid
  obtain ⟨τ,rs,ps⟩ := RamPotentialSweep.command_spec B M I (d u) false hM hB hindex hvertex (hd u)
    (fun i hi => hcuts _) ν ⟨hν.nValue,hν.n2Value,hcount,hrev,hν.total,hν.weights,hν.capacities,hpotential,
      (hroom.frame rp).1 _ (by simp),(hroom.frame rp).2⟩
  exact ⟨τ,rp.seq rs,ThresholdCutData.candidate false (d u) j,hjvalid,hjratio.trans hzeroRatio,
    by simpa only [hj,RamPotentialSweep.Selected] using ps.2.2⟩

end Lax455465Proofs.RamZeroCut
