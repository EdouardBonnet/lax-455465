import Lax455465Proofs.RamLargePotential
import Lax455465Proofs.RamPotentialSweep
import Lax455465Proofs.PotentialCandidates

set_option maxRecDepth 8192
namespace Lax455465Proofs.RamLargeCut
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar RamRegionContext
open Lax455465.RationalEncoding LargePotentialData
open scoped BigOperators NNRat

structure Input {n : ℕ} (I : RationalInstance n) (d : MetricMatrix.Matrix n)
    (Tin Tout : Finset (Fin n)) (σ : Env) : Prop where
  potential : RamLargePotential.Input I d Tin Tout σ
  n2Value : σ.vars "metric.n2"=n*n
  total : Stored "round.total" (RamRoundingInit.total I.weight) σ
  capacities : Prefix (RamUnsignedBuffer.encode (MetricMatrix.values I.capacity)) "flow.capacities" σ
  potentialRoom : RamLargePotential.Room n σ
  maskRoom : 2*n<(σ.arrs "cut.flags").length
  crossingRoom : 2*(n*n)<(σ.arrs "cut.crossing").length

def command : Com := .seq RamLargePotential.command (.seq (.assign "cut.count" (.var "metric.n")) RamPotentialSweep.command)
def cost (n M : ℕ) : ℕ := RamLargePotential.cost n M+RamPotentialSweep.cost n M+2

set_option maxHeartbeats 4800000 in
/-- Compute the large-ball potential and sweep all its actual thresholds.
Any proved bound on an admissible mathematical threshold transfers to the
cut mask produced by this fixed RAM command. -/
theorem command_spec (B M : ℕ) {n : ℕ} (I : RationalInstance n) (d : MetricMatrix.Matrix n)
    (Tin Tout : Finset (Fin n)) (hin : Tin.Nonempty) (hout : Tout.Nonempty)
    (hb : Bounds I d Tin Tout hin hout M) (hcuts : ∀ S,CutScoreHeight.Bounds I S M)
    (hM : 1≤M) (hB : 2*M^2+3<B) (hindex : 2*(n*n)+2<B) (hvertex : 2*n+2<B)
    (U : ℚ) (hgood : ∃ S∈CutSweeps.candidates (LargeBallRounding.potential I (MetricMatrix.rational d) Tin Tout hin hout),
      CutSweeps.admissibleQ I S ∧ CutSweeps.ratioQ I S≤U) :
    Spec B (Input I d Tin Tout) command
      (fun _ τ => ∃ S : Finset (Fin n),CutSweeps.admissibleQ I S ∧ CutSweeps.ratioQ I S≤U ∧
        Prefix (RamUnsignedBuffer.encode (CutScoreData.vertexFlags S)) "cut.flags" τ) (cost n M) := by
  let f := values I d Tin Tout hin hout
  let reversed := LargePotentialData.reversed I d Tin Tout hin hout
  have hf : ∀ v,LpInputSize.Height M (f v : ℚ) := by
    intro v
    dsimp only [f,values]
    split_ifs <;> exact SetDistanceData.height _ d _ _ M hb.distances v
  obtain ⟨S,hS,hvalid,hratio⟩ := hgood
  have hSmem : S∈CutSweeps.candidates (ThresholdCutData.potential reversed f) := by
    simpa only [f,reversed,LargePotentialData.potential_eq] using hS
  obtain ⟨j,hj,hjn,hjvalid,hjratio⟩ := RamPotentialSweep.selected_le I f reversed S hSmem hvalid
  rintro σ hσ
  obtain ⟨ν,rp,pp⟩ := RamLargePotential.command_spec B M I d Tin Tout hin hout hb hM hB hindex hvertex σ
    ⟨hσ.potential,hσ.potentialRoom⟩
  let μ := ν.setVar "cut.count" n
  have rc : Run B (.assign "cut.count" (.var "metric.n")) ν μ 2 :=
    Run.assign (by rw [evalB_var_iff]; exact ⟨pp.1.nValue.symm,pp.1.nValue ▸ (by omega : n<B)⟩)
  have htotal := RamRoundingConstants.storedFrame rp hσ.total (by decide) (by decide)
  have hcap : Prefix (RamUnsignedBuffer.encode (MetricMatrix.values I.capacity)) "flow.capacities" ν := by
    simpa only [Prefix,rp.frame_arr "flow.capacities" (by decide)] using hσ.capacities
  have hinput : RamThresholdCandidate.Input I f reversed μ := by
    exact ⟨by simpa [μ] using pp.1.nValue,
      by simpa [μ,rp.frame_var "metric.n2" (by decide)] using hσ.n2Value,
      by simp [μ],by simpa [μ] using pp.2.1,htotal,pp.1.weights,hcap,pp.2.2,
      by rw [show μ.arrs "cut.flags"=ν.arrs "cut.flags" from rfl,RamFrames.run_array_length rp]; exact hσ.maskRoom,
      by rw [show μ.arrs "cut.crossing"=ν.arrs "cut.crossing" from rfl,RamFrames.run_array_length rp]; exact hσ.crossingRoom⟩
  obtain ⟨τ,rs,ps⟩ := RamPotentialSweep.command_spec B M I f reversed hM hB hindex hvertex hf (fun i hi => hcuts _) μ hinput
  have hmask : Prefix (RamUnsignedBuffer.encode (CutScoreData.vertexFlags (ThresholdCutData.candidate reversed f j))) "cut.flags" τ := by
    simpa only [hj,RamPotentialSweep.Selected] using ps.2.2
  exact ⟨τ,(rp.seq (rc.seq rs)).mono (by dsimp [cost]; omega),
    ThresholdCutData.candidate reversed f j,hjvalid,hjratio.trans hratio,hmask⟩

/-- The geometric hypotheses of the large-ball lemma give the same 6W
guarantee for the cut actually constructed by the RAM implementation. -/
theorem large_ball_spec (B M : ℕ) {n : ℕ} (I : RationalInstance n) (d : MetricMatrix.Matrix n)
    (Tin Tout : Finset (Fin n)) (hin : Tin.Nonempty) (hout : Tout.Nonempty) (root : Fin n)
    (hb : Bounds I d Tin Tout hin hout M) (hcuts : ∀ S,CutScoreHeight.Bounds I S M)
    (hM : 1≤M) (hB : 2*M^2+3<B) (hindex : 2*(n*n)+2<B) (hvertex : 2*n+2<B)
    (htotal : 0<LargeBallRounding.total I) (hdiag : ∀ v,d v v=0)
    (hsep : 1≤LargeBallRounding.distanceSeparation I (MetricMatrix.rational d))
    (htri : ∀ u v w,(d u w : ℚ)≤(d u v : ℚ)+(d v w : ℚ))
    (hinRadius : ∀ s∈Tin,(d s root : ℚ)≤1/(4*LargeBallRounding.total I^2))
    (houtRadius : ∀ t∈Tout,(d root t : ℚ)≤1/(4*LargeBallRounding.total I^2))
    (hinMass : (2/3 : ℚ)*LargeBallRounding.total I≤LargeBallRounding.mass I Tin)
    (houtMass : (2/3 : ℚ)*LargeBallRounding.total I≤LargeBallRounding.mass I Tout) :
    Spec B (Input I d Tin Tout) command
      (fun _ τ => ∃ S : Finset (Fin n),CutSweeps.admissibleQ I S ∧
        CutSweeps.ratioQ I S≤6*(∑ u,∑ v,(I.capacity u v : ℚ)*(d u v : ℚ)) ∧
        Prefix (RamUnsignedBuffer.encode (CutScoreData.vertexFlags S)) "cut.flags" τ) (cost n M) := by
  obtain ⟨S,hS,hvalid,hratio⟩ := LargeBallRounding.round_correct I (MetricMatrix.rational d) Tin Tout hin hout root htotal
    (fun _ _ => NNRat.coe_nonneg _) (by intro v; simp [MetricMatrix.rational,hdiag]) hsep htri hinRadius houtRadius hinMass houtMass
  exact command_spec B M I d Tin Tout hin hout hb hcuts hM hB hindex hvertex _
    ⟨S,PotentialCandidates.round_mem I _ S hS,hvalid,hratio⟩

end Lax455465Proofs.RamLargeCut
