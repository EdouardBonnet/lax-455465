import Lax455465Proofs.RamPotentialChoice

set_option maxRecDepth 8192
namespace Lax455465Proofs.RamLargePotential
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar RamRegionContext
open Lax455465.RationalEncoding LargePotentialData
open scoped NNRat

structure Input {n : ℕ} (I : RationalInstance n) (d : MetricMatrix.Matrix n)
    (Tin Tout : Finset (Fin n)) (σ : Env) : Prop where
  nValue : σ.vars "metric.n"=n
  weights : Prefix (RamUnsignedBuffer.encode (List.ofFn I.weight)) "flow.weights" σ
  distances : Prefix (RamUnsignedBuffer.encode (MetricMatrix.values d)) "metric.old" σ
  inMask : Prefix (RamUnsignedBuffer.encode (CutScoreData.vertexFlags Tin)) "region.inMask" σ
  outMask : Prefix (RamUnsignedBuffer.encode (CutScoreData.vertexFlags Tout)) "region.outMask" σ

def sourceArrays : List String := ["flow.weights","metric.old","region.inMask","region.outMask"]
def scratchArrays : List String := ["potential.set","potential.values","region.in","region.out",
  "potential.to","potential.from","cut.potential"]
def Room (n : ℕ) (σ : Env) : Prop := ∀ a∈scratchArrays,2*n<(σ.arrs a).length

theorem Input.frame {B K : ℕ} {cmd : Com} {σ τ : Env} (rr : Run B cmd σ τ K)
    {n : ℕ} {I : RationalInstance n} {d : MetricMatrix.Matrix n} {Tin Tout : Finset (Fin n)}
    (h : Input I d Tin Tout σ) (hn : "metric.n"∉cmd.wvars)
    (ha : ∀ a∈sourceArrays,a∉cmd.warrs) : Input I d Tin Tout τ := by
  exact ⟨(rr.frame_var _ hn).trans h.nValue,
    by simpa only [Prefix,rr.frame_arr "flow.weights" (ha _ (by simp [sourceArrays]))] using h.weights,
    by simpa only [Prefix,rr.frame_arr "metric.old" (ha _ (by simp [sourceArrays]))] using h.distances,
    by simpa only [Prefix,rr.frame_arr "region.inMask" (ha _ (by simp [sourceArrays]))] using h.inMask,
    by simpa only [Prefix,rr.frame_arr "region.outMask" (ha _ (by simp [sourceArrays]))] using h.outMask⟩

theorem Room.frame {B K : ℕ} {cmd : Com} {σ τ : Env} (rr : Run B cmd σ τ K)
    {n : ℕ} (h : Room n σ) : Room n τ := by
  intro a ha
  rw [RamFrames.run_array_length rr]
  exact h a ha

theorem Room.stage {n : ℕ} {σ : Env} (h : Room n σ) (toSet : Bool) : RamSetPotential.Room n toSet σ := by
  intro a ha
  apply h a
  cases toSet <;> simp_all [scratchArrays,RamRootDistances.array,RamSetPotential.targetArray] <;> tauto

def command : Com := .seq (RamSetPotential.command false) (.seq (RamSetPotential.command true)
  (.seq (RamPotentialAverage.command false) (.seq (RamPotentialAverage.command true) RamPotentialChoice.command)))
def cost (n M : ℕ) : ℕ := 2*RamSetPotential.cost n+2*RamPotentialAverage.cost n M+24*n+80

set_option maxHeartbeats 4800000 in
/-- The complete large-ball potential program computes both set-distance
vectors and their original-weight averages, and chooses the same directed
potential used by the mathematical rounding theorem. -/
theorem command_spec (B M : ℕ) {n : ℕ} (I : RationalInstance n) (d : MetricMatrix.Matrix n)
    (Tin Tout : Finset (Fin n)) (hin : Tin.Nonempty) (hout : Tout.Nonempty)
    (hb : Bounds I d Tin Tout hin hout M) (hM : 1≤M) (hB : 2*M^2+3<B)
    (hindex : 2*(n*n)+2<B) (hvertex : 2*n+2<B) :
    Spec B (fun σ => Input I d Tin Tout σ ∧ Room n σ) command
      (fun _ τ => Input I d Tin Tout τ ∧
        τ.vars "cut.reversed"=(if reversed I d Tin Tout hin hout then 1 else 0) ∧
        Prefix (RamUnsignedBuffer.encode (List.ofFn (values I d Tin Tout hin hout))) "cut.potential" τ)
      (cost n M) := by
  rintro σ ⟨hσ,hroom⟩
  obtain ⟨σ1,r1,p1⟩ := RamSetPotential.command_spec B M false d Tout hout hM hB hindex hvertex hb.distances σ
    ⟨⟨hσ.nValue,hσ.distances,hσ.outMask⟩,hroom.stage false⟩
  have h1 := Input.frame r1 hσ (by decide) (by dsimp [sourceArrays]; decide)
  obtain ⟨σ2,r2,p2⟩ := RamSetPotential.command_spec B M true d Tin hin hM hB hindex hvertex hb.distances σ1
    ⟨⟨h1.nValue,h1.distances,h1.inMask⟩,(hroom.frame r1).stage true⟩
  have h2 := Input.frame r2 h1 (by decide) (by dsimp [sourceArrays]; decide)
  have hfrom2 : Prefix (RamUnsignedBuffer.encode (vector false d Tout hout)) "potential.from" σ2 := by
    simpa only [vector,Prefix,RamSetPotential.targetArray,Bool.false_eq_true,if_false,r2.frame_arr "potential.from" (by decide)] using p1.2
  obtain ⟨σ3,r3,p3⟩ := RamPotentialAverage.command_spec B M I false d Tout hout hB hvertex
    hb.weights hb.distances hb.fromProducts hb.fromPrefix σ2 ⟨h2.nValue,h2.weights,hfrom2⟩
  have h3 := Input.frame r3 h2 (by decide) (by dsimp [sourceArrays]; decide)
  have hto3 : Prefix (RamUnsignedBuffer.encode (vector true d Tin hin)) "potential.to" σ3 := by
    simpa only [vector,Prefix,RamSetPotential.targetArray,if_true,r3.frame_arr "potential.to" (by decide)] using p2.2
  obtain ⟨σ4,r4,p4⟩ := RamPotentialAverage.command_spec B M I true d Tin hin hB hvertex
    hb.weights hb.distances hb.toProducts hb.toPrefix σ3 ⟨h3.nValue,h3.weights,hto3⟩
  have h4 := Input.frame r4 h3 (by decide) (by dsimp [sourceArrays]; decide)
  have hfromAvg : Stored "potential.fromAvg" (average I false d Tout hout) σ4 :=
    RamRoundingConstants.storedFrame r4 p3 (by decide) (by decide)
  have hfrom4 : Prefix (RamUnsignedBuffer.encode (vector false d Tout hout)) "potential.from" σ4 := by
    simpa only [Prefix,(r3.seq r4).frame_arr "potential.from" (by decide)] using hfrom2
  have hto4 : Prefix (RamUnsignedBuffer.encode (vector true d Tin hin)) "potential.to" σ4 := by
    simpa only [Prefix,r4.frame_arr "potential.to" (by decide)] using hto3
  have rr4 := r1.seq (r2.seq (r3.seq r4))
  obtain ⟨τ,r5,p5⟩ := RamPotentialChoice.command_spec B M I d Tin Tout hin hout hb hB hvertex σ4
    ⟨h4.nValue,hfromAvg,p4,hfrom4,hto4,(hroom.frame rr4) _ (by simp [scratchArrays])⟩
  have rr := r1.seq (r2.seq (r3.seq (r4.seq r5)))
  exact ⟨τ,rr.mono (by dsimp [cost]; omega),Input.frame r5 h4 (by decide) (by dsimp [sourceArrays]; decide),p5⟩

end Lax455465Proofs.RamLargePotential
