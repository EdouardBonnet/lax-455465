import Lax455465Proofs.RamSetDistances
import Lax455465Proofs.RamArrayCopy

set_option maxRecDepth 8192
namespace Lax455465Proofs.RamSetPotential
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamRegionContext
open scoped NNRat

def maskArray (toSet : Bool) : String := if toSet then "region.inMask" else "region.outMask"
def targetArray (toSet : Bool) : String := if toSet then "potential.to" else "potential.from"
def Context {n : ℕ} (toSet : Bool) (d : MetricMatrix.Matrix n) (S : Finset (Fin n)) (σ : Env) : Prop :=
  σ.vars "metric.n"=n ∧ Prefix (RamUnsignedBuffer.encode (MetricMatrix.values d)) "metric.old" σ ∧
    Prefix (RamUnsignedBuffer.encode (CutScoreData.vertexFlags S)) (maskArray toSet) σ
def Room (n : ℕ) (toSet : Bool) (σ : Env) : Prop :=
  ∀ a∈["potential.set","potential.values",RamRootDistances.array toSet,targetArray toSet],2*n<(σ.arrs a).length

theorem frame {B K : ℕ} {cmd : Com} {σ τ : Env} (rr : Run B cmd σ τ K)
    {n : ℕ} {toSet : Bool} {d : MetricMatrix.Matrix n} {S : Finset (Fin n)} (h : Context toSet d S σ)
    (hx : "metric.n"∉cmd.wvars) (hd : "metric.old"∉cmd.warrs) (hs : maskArray toSet∉cmd.warrs) : Context toSet d S τ := by
  simpa only [Context,Prefix,rr.frame_var "metric.n" hx,rr.frame_arr "metric.old" hd,rr.frame_arr (maskArray toSet) hs] using h

def setup : Com := .seq (.assign "cut.count" (.var "metric.n"))
  (.assign "copy.count" (.mul (.lit 2) (.var "metric.n")))
def command (toSet : Bool) : Com := .seq setup
  (.seq (RamArrayCopy.command (maskArray toSet) "potential.set" "copy.count")
    (.seq (RamSetDistances.command toSet) (RamArrayCopy.command "potential.values" (targetArray toSet) "copy.count")))
def cost (n : ℕ) : ℕ := RamSetDistances.cost n+48*n+18

theorem encoded_bound (B M : ℕ) (qs : List ℚ≥0) (hMB : M<B)
    (hq : ∀ q∈qs,LpInputSize.Height M (q : ℚ)) : ∀ x∈RamUnsignedBuffer.encode qs,x<B := by
  intro x hx
  simp only [RamUnsignedBuffer.encode,List.mem_flatMap] at hx
  obtain ⟨q,hq',hx⟩ := hx
  simp only [Lax455465.RationalEncoding.encodeRational,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl
  · exact (num_bound (hq q hq')).trans_lt hMB
  · exact (den_bound (hq q hq')).trans_lt hMB

set_option maxHeartbeats 3200000 in
/-- Materialize one set-distance potential from the region loop's mask and
original metric matrix, retaining a separate vector for each orientation. -/
theorem command_spec (B M : ℕ) {n : ℕ} (toSet : Bool) (d : MetricMatrix.Matrix n)
    (S : Finset (Fin n)) (hS : S.Nonempty) (hM : 1≤M) (hB : 2*M^2+3<B)
    (hindex : 2*(n*n)+2<B) (hvertex : 2*n+2<B) (hd : ∀ u v,LpInputSize.Height M (d u v : ℚ)) :
    Spec B (fun σ => Context toSet d S σ ∧ Room n toSet σ) (command toSet)
      (fun _ τ => Context toSet d S τ ∧ Prefix (RamUnsignedBuffer.encode
        (List.ofFn (SetDistanceData.distance toSet d S hS))) (targetArray toSet) τ) (cost n) := by
  have h1 : 1<B := by nlinarith
  have hMB : M<B := by nlinarith
  let mask := CutScoreData.vertexFlags S
  let qs := List.ofFn (SetDistanceData.distance toSet d S hS)
  have hmasklen : (RamUnsignedBuffer.encode mask).length=2*n := by simp [mask,CutScoreData.vertexFlags,MaskedMassData.flags]
  have hqslen : (RamUnsignedBuffer.encode qs).length=2*n := by simp [qs]
  have hmaskwords : ∀ x∈RamUnsignedBuffer.encode mask,x<B := by
    apply encoded_bound B 1 mask h1
    intro q hq
    obtain ⟨v,rfl⟩ := List.mem_ofFn.mp hq
    change LpInputSize.Height 1 (((if ResidualData.mask S v then 1 else 0) : ℚ≥0) : ℚ)
    split_ifs <;> norm_num [LpInputSize.Height]
  have hqswords : ∀ x∈RamUnsignedBuffer.encode qs,x<B := by
    apply encoded_bound B M qs hMB
    intro q hq
    obtain ⟨v,rfl⟩ := List.mem_ofFn.mp hq
    exact SetDistanceData.height toSet d S hS M hd v
  rintro σ ⟨hσ,hroom⟩
  let ν := (σ.setVar "cut.count" n).setVar "copy.count" (2*n)
  have rsetup : Run B setup σ ν 6 := by
    have r1 : Run B (.assign "cut.count" (.var "metric.n")) σ (σ.setVar "cut.count" n) 2 :=
      Run.assign (by rw [evalB_var_iff]; exact ⟨hσ.1.symm,hσ.1 ▸ (by omega : n<B)⟩)
    have hn : (σ.setVar "cut.count" n).vars "metric.n"=n := by simpa using hσ.1
    have r2 : Run B (.assign "copy.count" (.mul (.lit 2) (.var "metric.n"))) (σ.setVar "cut.count" n) ν 4 :=
      Run.assign (evalB_bin (op := .mul) (evalB_lit (by omega))
        (by rw [evalB_var_iff]; exact ⟨hn.symm,hn ▸ (by omega : n<B)⟩) (by dsimp [Bop.apply]; omega))
    exact r1.seq r2
  have hν := frame rsetup hσ (by decide) (by decide) (by cases toSet <;> decide)
  obtain ⟨μ,rc,pc⟩ := RamArrayCopy.command_spec B (RamUnsignedBuffer.encode mask) (maskArray toSet)
    "potential.set" "copy.count" h1 (by rw [hmasklen]; omega) hmaskwords (by cases toSet <;> decide) (by decide) ν
    ⟨hν.2.2,by simp [ν,hmasklen],by rw [hmasklen]; exact (hroom _ (by simp [Room])).le⟩
  have hμ := frame rc hν (by cases toSet <;> decide) (by cases toSet <;> decide) (by cases toSet <;> decide)
  have hcount : μ.vars "cut.count"=n := by rw [rc.frame_var _ (by cases toSet <;> decide)]; simp [ν]
  have rpre := rsetup.seq rc
  obtain ⟨ξ,rd,pd⟩ := RamSetDistances.command_spec B M toSet d S hS hM hB hindex hvertex hd μ
    ⟨⟨hμ.1,hcount,hμ.2.1,pc.2⟩,
      by rw [RamFrames.run_array_length rpre]; exact hroom _ (by simp [Room]),
      by rw [RamFrames.run_array_length rpre]; exact hroom _ (by simp [Room])⟩
  have rbefore := rpre.seq rd
  obtain ⟨τ,rs,ps⟩ := RamArrayCopy.command_spec B (RamUnsignedBuffer.encode qs) "potential.values"
    (targetArray toSet) "copy.count" h1 (by rw [hqslen]; omega) hqswords (by cases toSet <;> decide) (by decide) ξ
    ⟨pd.2,by rw [rd.frame_var _ (by cases toSet <;> decide),rc.frame_var _ (by cases toSet <;> decide)]; simp [ν,hqslen],
      by rw [hqslen,RamFrames.run_array_length rbefore]; exact (hroom _ (by simp [Room])).le⟩
  have rr := rsetup.seq (rc.seq (rd.seq rs))
  exact ⟨τ,rr.mono (by rw [hmasklen,hqslen]; dsimp [cost]; omega),
    frame rr hσ (by cases toSet <;> decide) (by cases toSet <;> decide) (by cases toSet <;> decide),ps.2⟩

end Lax455465Proofs.RamSetPotential
