import Lax455465Proofs.RamRoundingConstants
import Lax455465Proofs.RamRootDistances
import Lax455465Proofs.RamRadiusCandidates
import Lax455465Proofs.RamSelectedRegion

set_option maxRecDepth 4096
namespace Lax455465Proofs.RamRegionSetup
open RegionQueryData Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamUnsignedScalar RamVirtualState
open scoped NNRat

def query {n : ℕ} (weights : Fin n → ℚ≥0) (capacity length : MetricMatrix.Matrix n)
    (root : Fin n) (seed beta : ℚ≥0) : Query n :=
  ⟨weights,capacity,length,length root,(fun v => length v root),seed,beta,0⟩

structure Input {n : ℕ} (weights : Fin n → ℚ≥0) (capacity length : MetricMatrix.Matrix n)
    (root : Fin n) (seed beta delta : ℚ≥0) (k : ℕ) (σ : Env) : Prop where
  nValue : σ.vars "metric.n"=n
  n2Value : σ.vars "metric.n2"=n*n
  rootValue : σ.vars "region.root"=root.val
  stepsValue : σ.vars "round.steps"=k
  seedData : Stored "round.seed" seed σ
  betaData : Stored "round.slope" beta σ
  deltaData : Stored "round.delta" delta σ
  unitData : Stored "round.gridStep" (delta/(k : ℚ≥0)) σ
  weightsData : Prefix (RamUnsignedBuffer.encode (List.ofFn weights)) "region.weights" σ
  capacityData : Prefix (RamUnsignedBuffer.encode (MetricMatrix.values capacity)) "region.capacities" σ
  lengthData : Prefix (RamUnsignedBuffer.encode (MetricMatrix.values length)) "metric.old" σ

structure Room (n count : ℕ) (σ : Env) : Prop where
  outRoom : 2*n<(σ.arrs "region.out").length
  inRoom : 2*n<(σ.arrs "region.in").length
  radiusRoom : 2*count<(σ.arrs "region.radii").length
  outMaskRoom : 2*n<(σ.arrs "region.outMask").length
  inMaskRoom : 2*n<(σ.arrs "region.inMask").length
  crossingRoom : 2*(n*n)<(σ.arrs "region.crossing").length

def names : List String := ["metric.n","metric.n2","region.root","round.steps",
  "round.seed.n","round.seed.d","round.slope.n","round.slope.d",
  "round.delta.n","round.delta.d","round.gridStep.n","round.gridStep.d"]
def arrays : List String := ["region.weights","region.capacities","metric.old"]

theorem frame {B K : ℕ} {cmd : Com} {σ τ : Env} (rr : Run B cmd σ τ K)
    {n : ℕ} {weights : Fin n → ℚ≥0} {capacity length : MetricMatrix.Matrix n} {root : Fin n}
    {seed beta delta : ℚ≥0} {k : ℕ} (h : Input weights capacity length root seed beta delta k σ)
    (hx : ∀ x ∈ names, x∉cmd.wvars) (ha : ∀ a ∈ arrays, a∉cmd.warrs) :
    Input weights capacity length root seed beta delta k τ := by
  refine ⟨(rr.frame_var _ (hx _ (by simp [names]))).trans h.nValue,
    (rr.frame_var _ (hx _ (by simp [names]))).trans h.n2Value,
    (rr.frame_var _ (hx _ (by simp [names]))).trans h.rootValue,
    (rr.frame_var _ (hx _ (by simp [names]))).trans h.stepsValue,?_,?_,?_,?_,?_,?_,?_⟩
  · exact RamRoundingConstants.storedFrame rr h.seedData (hx _ (by simp [names])) (hx _ (by simp [names]))
  · exact RamRoundingConstants.storedFrame rr h.betaData (hx _ (by simp [names])) (hx _ (by simp [names]))
  · exact RamRoundingConstants.storedFrame rr h.deltaData (hx _ (by simp [names])) (hx _ (by simp [names]))
  · exact RamRoundingConstants.storedFrame rr h.unitData (hx _ (by simp [names])) (hx _ (by simp [names]))
  · simpa only [Prefix,rr.frame_arr "region.weights" (ha _ (by simp [arrays]))] using h.weightsData
  · simpa only [Prefix,rr.frame_arr "region.capacities" (ha _ (by simp [arrays]))] using h.capacityData
  · simpa only [Prefix,rr.frame_arr "metric.old" (ha _ (by simp [arrays]))] using h.lengthData

theorem Room.frame {B K n count : ℕ} {cmd : Com} {σ τ : Env} (rr : Run B cmd σ τ K)
    (h : Room n count σ) : Room n count τ := by
  exact ⟨by rw [RamFrames.run_array_length rr "region.out"]; exact h.outRoom,
    by rw [RamFrames.run_array_length rr "region.in"]; exact h.inRoom,
    by rw [RamFrames.run_array_length rr "region.radii"]; exact h.radiusRoom,
    by rw [RamFrames.run_array_length rr "region.outMask"]; exact h.outMaskRoom,
    by rw [RamFrames.run_array_length rr "region.inMask"]; exact h.inMaskRoom,
    by rw [RamFrames.run_array_length rr "region.crossing"]; exact h.crossingRoom⟩

def setup : Com := .seq (.assign "find.count" (.var "radius.count"))
  (.seq (.assign "region.radius.n" (.lit 0)) (.assign "region.radius.d" (.lit 1)))
def command : Com := .seq (RamRootDistances.command true) (.seq (RamRootDistances.command false)
  (.seq RamRadiusCandidates.command (.seq setup RamSelectedRegion.command)))

def cost (n k M H : ℕ) : ℕ :=
  (36*(M^2).size+RamRadiusSearch.queryCost n H+160)*(k+1+2*n)+84*n+RamRadiusSearch.queryCost n H+80

set_option maxHeartbeats 2400000 in
/-- For a runtime root, extract both metric distance vectors, generate the
exact candidate buffer, and execute the selected-region search. All query
inputs come from the existing residual graph and metric buffers. -/
theorem command_spec (B M H : ℕ) {n : ℕ} (weights : Fin n → ℚ≥0)
    (capacity length : MetricMatrix.Matrix n) (root : Fin n) (seed beta delta : ℚ≥0) (k : ℕ)
    (hk : k≤M) (hB : 2*M^2+3<B) (hquery : 2*(2^H)^2+3<B)
    (hindex : 2*(n*n)+2<B) (hvertex : 2*n+2<B) (hradius : 2*(k+1+2*n)+2<B)
    (hl : ∀ u v, LpInputSize.Height M (length u v : ℚ))
    (hd : LpInputSize.Height M (delta : ℚ)) (hu : LpInputSize.Height M ((delta/(k : ℚ≥0) : ℚ≥0) : ℚ))
    (hb : ∀ i, ∀ hi : i<(RadiusData.candidates (length root) (fun v => length v root) k delta).length,
      RegionQueryHeight.Bounds (RadiusSearchData.atRadius (query weights capacity length root seed beta)
        (RadiusData.candidates (length root) (fun v => length v root) k delta)[i]) H) :
    Spec B (fun σ => Input weights capacity length root seed beta delta k σ ∧ Room n (k+1+2*n) σ)
      command (fun _ τ => RamRadiusSearch.Context (query weights capacity length root seed beta)
        (RadiusData.candidates (length root) (fun v => length v root) k delta) τ ∧
        RamFind.Matches (RamFind.first (RadiusSearchData.predicate (query weights capacity length root seed beta)
          (RadiusData.candidates (length root) (fun v => length v root) k delta)) (k+1+2*n)) τ ∧
        RamSelectedRegion.Selected (query weights capacity length root seed beta)
          (RadiusData.candidates (length root) (fun v => length v root) k delta) τ)
      (cost n k M H) := by
  have hMB : M<B := by nlinarith
  let q := query weights capacity length root seed beta
  let radii := RadiusData.candidates (length root) (fun v => length v root) k delta
  have hlen : radii.length=k+1+2*n := RadiusData.length_candidates _ _ _ _
  rintro σ ⟨hσ,hroom⟩
  obtain ⟨σ1,r1,p1⟩ := RamRootDistances.command_spec B M true root length hMB (by omega) (by omega) hindex
    (fun u v => RamRegionContext.num_bound (hl u v)) (fun u v => RamRegionContext.den_bound (hl u v)) σ
    ⟨⟨hσ.nValue,hσ.rootValue,hσ.lengthData⟩,hroom.outRoom⟩
  have h1 := frame r1 hσ (by dsimp [names]; decide) (by dsimp [arrays]; decide)
  have room1 := Room.frame r1 hroom
  obtain ⟨σ2,r2,p2⟩ := RamRootDistances.command_spec B M false root length hMB (by omega) (by omega) hindex
    (fun u v => RamRegionContext.num_bound (hl u v)) (fun u v => RamRegionContext.den_bound (hl u v)) σ1
    ⟨⟨h1.nValue,h1.rootValue,h1.lengthData⟩,room1.inRoom⟩
  have h2 := frame r2 h1 (by dsimp [names]; decide) (by dsimp [arrays]; decide)
  have room2 := Room.frame r2 room1
  have hout2 : Prefix (RamUnsignedBuffer.encode (List.ofFn (length root))) "region.out" σ2 := by
    simpa only [RamRootDistances.vector,RamRootDistances.array,if_true,Prefix,r2.frame_arr "region.out" (by decide)] using p1.2
  obtain ⟨σ3,r3,p3⟩ := RamRadiusCandidates.command_spec B M (length root) (fun v => length v root) k delta hk hB hradius
    (RamRegionContext.num_bound hu) (RamRegionContext.den_bound hu)
    (RamRegionContext.num_bound hd) (RamRegionContext.den_bound hd)
    (fun v => RamRegionContext.num_bound (hl root v)) (fun v => RamRegionContext.den_bound (hl root v))
    (fun v => RamRegionContext.num_bound (hl v root)) (fun v => RamRegionContext.den_bound (hl v root)) σ2
    ⟨⟨h2.nValue,h2.stepsValue,h2.deltaData,h2.unitData,hout2,
      by simpa only [RamRootDistances.vector,RamRootDistances.array,Bool.false_eq_true,if_false] using p2.2⟩,room2.radiusRoom⟩
  have h3 := frame r3 h2 (by dsimp [names]; decide) (by dsimp [arrays]; decide)
  have room3 := Room.frame r3 room2
  let σ4 := ((σ3.setVar "find.count" (k+1+2*n)).setVar "region.radius.n" 0).setVar "region.radius.d" 1
  have r4 : Run B setup σ3 σ4 6 :=
    (Run.assign (by rw [evalB_var_iff]; exact ⟨p3.1.count.symm,p3.1.count ▸ (by omega : k+1+2*n<B)⟩)).seq
      ((Run.assign (evalB_lit (by omega))).seq (Run.assign (evalB_lit (by omega))))
  have h4 := frame r4 h3 (by dsimp [names]; decide) (by dsimp [arrays]; decide)
  have room4 := Room.frame r4 room3
  have hctx : RamRadiusSearch.Context q radii σ4 := by
    refine ⟨⟨0,?_⟩,?_,by simp [σ4,hlen],room4.outMaskRoom,room4.inMaskRoom,room4.crossingRoom⟩
    · refine ⟨h4.nValue,h4.n2Value,by simp [RamUnsignedScalar.Stored,RadiusSearchData.atRadius,σ4],
        h4.seedData,h4.betaData,h4.weightsData,h4.capacityData,h4.lengthData,?_,?_⟩
      · have rr := r3.seq r4
        simpa only [q,query,RadiusSearchData.atRadius,Prefix,rr.frame_arr "region.out" (by decide)] using hout2
      · have rr := r3.seq r4
        simpa only [q,query,RadiusSearchData.atRadius,RamRootDistances.vector,RamRootDistances.array,Bool.false_eq_true,if_false,
          Prefix,rr.frame_arr "region.in" (by decide)] using p2.2
    · simpa only [radii,Prefix,r4.frame_arr "region.radii" (by decide)] using p3.2
  obtain ⟨τ,r5,p5⟩ := RamSelectedRegion.command_spec B H q radii hb hquery hindex hvertex (by rwa [hlen]) σ4 hctx
  have rr := r1.seq (r2.seq (r3.seq (r4.seq r5)))
  refine ⟨τ,rr.mono (by simp only [hlen,cost]; ring_nf; omega),p5.1,?_,p5.2.2⟩
  simpa only [hlen] using p5.2.1

end Lax455465Proofs.RamRegionSetup
