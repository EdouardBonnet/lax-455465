import Lax455465Proofs.CutScoreHeight
import Lax455465Proofs.RamRoundingConstants

namespace Lax455465Proofs.RamCutMeasures
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar RamRegionContext
open Lax455465.RationalEncoding CutScoreData MetricMatrix
open scoped NNRat

structure Input {n : ℕ} (I : RationalInstance n) (S : Finset (Fin n)) (σ : Env) : Prop where
  nValue : σ.vars "metric.n"=n
  n2Value : σ.vars "metric.n2"=n*n
  totalData : Stored "round.total" (RamRoundingInit.total I.weight) σ
  weightsData : Prefix (RamUnsignedBuffer.encode (List.ofFn I.weight)) "flow.weights" σ
  capacityData : Prefix (RamUnsignedBuffer.encode (values I.capacity)) "flow.capacities" σ
  maskData : Prefix (RamUnsignedBuffer.encode (vertexFlags S)) "cut.flags" σ

def command : Com := .seq (RamArcMask.command (some true) "cut.flags" "cut.crossing")
  (.seq (.assign "sum.count" (.var "metric.n2"))
    (.seq (RamMaskedSum.command "flow.capacities" "cut.crossing") (.seq (save "cut.capacity")
      (.seq (.assign "sum.count" (.var "metric.n"))
        (.seq (RamMaskedSum.command "flow.weights" "cut.flags") (save "cut.mass"))))))

set_option maxHeartbeats 2400000 in
/-- Score a candidate shore using the actual graph and canonical membership
buffer: compute its outward capacity and its original vertex mass. -/
theorem command_spec (B M : ℕ) {n : ℕ} (I : RationalInstance n) (S : Finset (Fin n)) (hM : 1≤M)
    (hb : CutScoreHeight.Bounds I S M) (hB : 2*M^2+3<B) (hindex : 2*(n*n)+2<B) (hvertex : 2*n+2<B) :
    Spec B (fun σ => Input I S σ ∧ 2*(n*n)<(σ.arrs "cut.crossing").length) command
      (fun _ τ => Input I S τ ∧ Stored "cut.capacity" (capacity I S) τ ∧ Stored "cut.mass" (mass I S) τ)
      ((36*(M^2).size+234)*(n*n)+(36*(M^2).size+152)*n+52) := by
  have hMB : M<B := by nlinarith
  let ws := List.ofFn I.weight
  let vs := vertexFlags S
  let cs := values I.capacity
  let es := values (arcFlags S)
  have hws : ws.length=n := List.length_ofFn
  have hvs : vs.length=n := List.length_ofFn
  have hcs : cs.length=n*n := length_values _
  have hes : es.length=n*n := length_values _
  have hwn : ∀ q∈ws,q.num≤M := by
    intro q hq; obtain ⟨v,rfl⟩ := List.mem_ofFn.mp hq; exact num_bound (hb.weightsBound v)
  have hwd : ∀ q∈ws,q.den≤M := by
    intro q hq; obtain ⟨v,rfl⟩ := List.mem_ofFn.mp hq; exact den_bound (hb.weightsBound v)
  have hcn : ∀ q∈cs,q.num≤M := by
    intro q hq; obtain ⟨v,rfl⟩ := List.mem_ofFn.mp hq; exact num_bound (hb.capacityBound _ _)
  have hcd : ∀ q∈cs,q.den≤M := by
    intro q hq; obtain ⟨v,rfl⟩ := List.mem_ofFn.mp hq; exact den_bound (hb.capacityBound _ _)
  have hvn : ∀ q∈vs,q.num≤M := by
    intro q hq; obtain ⟨v,rfl⟩ := List.mem_ofFn.mp hq
    by_cases hv : v∈S <;> simp [vertexFlags,MaskedMassData.flags,ResidualData.mask,hv] <;> omega
  have hvd : ∀ q∈vs,q.den≤M := by
    intro q hq; obtain ⟨v,rfl⟩ := List.mem_ofFn.mp hq
    by_cases hv : v∈S <;> simp [vertexFlags,MaskedMassData.flags,ResidualData.mask,hv] <;> omega
  have hen : ∀ q∈es,q.num≤M := by
    intro q hq; obtain ⟨v,rfl⟩ := List.mem_ofFn.mp hq
    dsimp only [arcFlags,RamArcMask.matrix]
    cases RamBooleanArithmetic.flag (some true) (ResidualData.mask S _) (ResidualData.mask S _) <;>
      simp [RamBooleanArithmetic.bit] <;> omega
  have hed : ∀ q∈es,q.den≤M := by
    intro q hq; obtain ⟨v,rfl⟩ := List.mem_ofFn.mp hq
    dsimp only [arcFlags,RamArcMask.matrix]
    cases RamBooleanArithmetic.flag (some true) (ResidualData.mask S _) (ResidualData.mask S _) <;>
      simp [RamBooleanArithmetic.bit] <;> omega
  rintro σ ⟨hσ,hroom⟩
  obtain ⟨σ1,r1,p1⟩ := RamArcMask.command_spec B (some true) "cut.flags" "cut.crossing" (ResidualData.mask S)
    (by decide) (by nlinarith) (by omega) (by omega) hindex hvertex σ
    ⟨⟨hσ.nValue,hσ.n2Value,hσ.maskData⟩,hroom⟩
  let σ2 := σ1.setVar "sum.count" (n*n)
  have r2 : Run B (.assign "sum.count" (.var "metric.n2")) σ1 σ2 2 :=
    Run.assign (by rw [evalB_var_iff]; exact ⟨p1.1.2.1.symm,p1.1.2.1 ▸ (by omega : n*n<B)⟩)
  have r12 := r1.seq r2
  obtain ⟨σ3,r3,p3⟩ := RamMaskedSum.command_spec B M "flow.capacities" "cut.crossing" cs es
    (by rw [hes,hcs]) hB (by rwa [hcs]) hcn hcd hen hed
    (fun i => num_bound (hb.capacityPrefix i)) (fun i => den_bound (hb.capacityPrefix i)) σ2
    ⟨by simp [σ2,hcs],by simpa only [cs,Prefix,r12.frame_arr "flow.capacities" (by decide)] using hσ.capacityData,
      by simpa only [es,arcFlags,Prefix,σ2,arrs_setVar] using p1.2⟩
  obtain ⟨σ4,r4,p4⟩ := save_spec B "cut.capacity" (capacity I S)
    ((num_bound hb.cutCapacityBound).trans_lt hMB) ((den_bound hb.cutCapacityBound).trans_lt hMB) (by decide) σ3 p3.2
  have rbefore := r1.seq (r2.seq (r3.seq r4))
  have hn : σ4.vars "metric.n"=n := (rbefore.frame_var _ (by decide)).trans hσ.nValue
  let σ5 := σ4.setVar "sum.count" n
  have r5 : Run B (.assign "sum.count" (.var "metric.n")) σ4 σ5 2 :=
    Run.assign (by rw [evalB_var_iff]; exact ⟨hn.symm,hn ▸ (by omega : n<B)⟩)
  have rprior := r1.seq (r2.seq (r3.seq (r4.seq r5)))
  obtain ⟨σ6,r6,p6⟩ := RamMaskedSum.command_spec B M "flow.weights" "cut.flags" ws vs
    (by rw [hvs,hws]) hB (by rwa [hws]) hwn hwd hvn hvd
    (fun i => num_bound (hb.massPrefix i)) (fun i => den_bound (hb.massPrefix i)) σ5
    ⟨by simp [σ5,hws],by simpa only [ws,Prefix,rprior.frame_arr "flow.weights" (by decide)] using hσ.weightsData,
      by simpa only [vs,Prefix,rprior.frame_arr "cut.flags" (by decide)] using hσ.maskData⟩
  obtain ⟨τ,r7,p7⟩ := save_spec B "cut.mass" (mass I S)
    ((num_bound hb.massBound).trans_lt hMB) ((den_bound hb.massBound).trans_lt hMB) (by decide) σ6 p6.2
  have rr := r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq r7)))))
  refine ⟨τ,rr.mono (by simp only [hws,hcs]; nlinarith),?_,?_,p7⟩
  · exact ⟨(rr.frame_var _ (by decide)).trans hσ.nValue,(rr.frame_var _ (by decide)).trans hσ.n2Value,
      RamRoundingConstants.storedFrame rr hσ.totalData (by decide) (by decide),
      by simpa only [Prefix,rr.frame_arr "flow.weights" (by decide)] using hσ.weightsData,
      by simpa only [Prefix,rr.frame_arr "flow.capacities" (by decide)] using hσ.capacityData,
      by simpa only [Prefix,rr.frame_arr "cut.flags" (by decide)] using hσ.maskData⟩
  · exact RamRoundingConstants.storedFrame (r5.seq (r6.seq r7)) p4 (by decide) (by decide)

end Lax455465Proofs.RamCutMeasures
