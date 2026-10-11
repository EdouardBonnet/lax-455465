import Lax455465Proofs.RadiusSearchData
import Lax455465Proofs.RamRegionQuery
import Lax455465Proofs.RamArrayScalar
import Lax455465Proofs.RamFind

set_option maxRecDepth 4096
namespace Lax455465Proofs.RamRadiusSearch
open RadiusSearchData RegionQueryData RamRegionContext Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamUnsignedScalar RamVirtualState
open scoped NNRat

def queryCost (n H : ℕ) : ℕ := (288*H+880)*(n*n)+(144*H+584)*n+144*H+554

def sourceVariables : List String := ["metric.n","metric.n2","round.seed.n","round.seed.d","round.slope.n","round.slope.d","find.count"]
def sourceArrays : List String := RamRegionContext.arrays ++ ["region.radii"]

structure Context {n : ℕ} (q : Query n) (radii : List ℚ≥0) (σ : Env) : Prop where
  input : ∃ r : ℚ≥0, Input (atRadius q r) σ
  radiusData : Prefix (RamUnsignedBuffer.encode radii) "region.radii" σ
  count : σ.vars "find.count"=radii.length
  outRoom : 2*n < (σ.arrs "region.outMask").length
  inRoom : 2*n < (σ.arrs "region.inMask").length
  crossingRoom : 2*(n*n) < (σ.arrs "region.crossing").length

theorem replaceRadius {B K : ℕ} {cmd : Com} {σ τ : Env} (hr : Run B cmd σ τ K)
    {n : ℕ} {q : Query n} {radii : List ℚ≥0} {r : ℚ≥0} (h : Context q radii σ)
    (hstore : Stored "region.radius" r τ)
    (hx : ∀ x ∈ sourceVariables, x ∉ cmd.wvars) (ha : ∀ a ∈ sourceArrays, a ∉ cmd.warrs) :
    Context q radii τ := by
  obtain ⟨s,hs⟩ := h.input
  have hi : Input (atRadius q r) τ := by
    refine ⟨(hr.frame_var _ (hx _ (by simp [sourceVariables]))).trans hs.nValue,
      (hr.frame_var _ (hx _ (by simp [sourceVariables]))).trans hs.n2Value,hstore,?_,?_,?_,?_,?_,?_,?_⟩
    · simpa only [atRadius,Stored,String.reduceAppend,hr.frame_var "round.seed.n" (hx _ (by simp [sourceVariables])),hr.frame_var "round.seed.d" (hx _ (by simp [sourceVariables]))] using hs.seedData
    · simpa only [atRadius,Stored,String.reduceAppend,hr.frame_var "round.slope.n" (hx _ (by simp [sourceVariables])),hr.frame_var "round.slope.d" (hx _ (by simp [sourceVariables]))] using hs.betaData
    · simpa only [atRadius,Prefix,hr.frame_arr "region.weights" (ha _ (by simp [sourceArrays,RamRegionContext.arrays]))] using hs.weightsData
    · simpa only [atRadius,Prefix,hr.frame_arr "region.capacities" (ha _ (by simp [sourceArrays,RamRegionContext.arrays]))] using hs.capacityData
    · simpa only [atRadius,Prefix,hr.frame_arr "metric.old" (ha _ (by simp [sourceArrays,RamRegionContext.arrays]))] using hs.lengthData
    · simpa only [atRadius,Prefix,hr.frame_arr "region.out" (ha _ (by simp [sourceArrays,RamRegionContext.arrays]))] using hs.outData
    · simpa only [atRadius,Prefix,hr.frame_arr "region.in" (ha _ (by simp [sourceArrays,RamRegionContext.arrays]))] using hs.inData
  exact ⟨⟨r,hi⟩,by simpa only [Prefix,hr.frame_arr "region.radii" (ha _ (by simp [sourceArrays]))] using h.radiusData,
    (hr.frame_var _ (hx _ (by simp [sourceVariables]))).trans h.count,
    by rw [RamFrames.run_array_length hr "region.outMask"]; exact h.outRoom,
    by rw [RamFrames.run_array_length hr "region.inMask"]; exact h.inRoom,
    by rw [RamFrames.run_array_length hr "region.crossing"]; exact h.crossingRoom⟩

def Answer {n : ℕ} (q : Query n) (σ : Env) : Prop :=
  Masks q σ ∧ Stored "region.outMass" (BallMassData.mass q.weights q.outDistance q.radius) σ ∧
    Stored "region.inMass" (BallMassData.mass q.weights q.inDistance q.radius) σ ∧
    Stored "region.boundary" (boundary q) σ ∧ Stored "region.volume" (volume q) σ ∧
    Stored "query.bound" (bound q) σ ∧ σ.vars "find.ok" = if accepted q then 1 else 0

def test : Com := .seq (RamArrayScalar.command "region.radii" "find.i" "region.radius") RamRegionQuery.command

set_option maxHeartbeats 1800000 in
/-- Every native scan test loads the actual candidate word and computes its
exact region predicate. Static query data survive all candidate tests. -/
theorem test_answer_spec (B H : ℕ) {n : ℕ} (q : Query n) (radii : List ℚ≥0)
    (i : ℕ) (hi : i<radii.length) (hb : RegionQueryHeight.Bounds (atRadius q radii[i]) H)
    (hB : 2*(2^H)^2+3 < B) (hindex : 2*(n*n)+2 < B) (hvertex : 2*n+2 < B)
    (hposition : 2*i+1 < B) :
    Spec B (fun σ => Context q radii σ ∧ σ.vars "find.i"=i) test
      (fun _ τ => Context q radii τ ∧ Answer (atRadius q radii[i]) τ)
      (queryCost n H+18) := by
  have hn : radii[i].num<B := (num_bound hb.radiusBound).trans_lt (by nlinarith [(Nat.one_le_two_pow : 1≤2^H)])
  have hd : radii[i].den<B := (den_bound hb.radiusBound).trans_lt (by nlinarith [(Nat.one_le_two_pow : 1≤2^H)])
  rintro σ ⟨hctx,hidx⟩
  obtain ⟨ν,rr,pr⟩ := RamArrayScalar.command_spec B "region.radii" "find.i" "region.radius" radii i hi
    (by omega) hposition hn hd (by decide) (by decide) σ ⟨hctx.radiusData,hidx⟩
  have hν := replaceRadius rr hctx pr (by dsimp [sourceVariables]; decide) (by dsimp [sourceArrays,RamRegionContext.arrays]; decide)
  obtain ⟨s,hs⟩ := hctx.input
  have hiν : Input (atRadius q radii[i]) ν := by
    -- The loaded scalar fixes the otherwise existential radius.
    obtain ⟨r,hr⟩ := hν.input
    refine ⟨hr.nValue,hr.n2Value,pr,hr.seedData,hr.betaData,hr.weightsData,hr.capacityData,hr.lengthData,hr.outData,hr.inData⟩
  obtain ⟨τ,rq,pq⟩ := RamRegionQuery.command_spec B H (atRadius q radii[i]) hb hB hindex hvertex ν
    ⟨hiν,hν.outRoom,hν.inRoom,hν.crossingRoom⟩
  have hτ := replaceRadius rq hν pq.1.input.radiusData (by dsimp [sourceVariables]; decide) (by dsimp [sourceArrays,RamRegionContext.arrays]; decide)
  exact ⟨τ,(rr.seq rq).mono (by dsimp [queryCost]; omega),hτ,pq⟩

theorem test_spec (B H : ℕ) {n : ℕ} (q : Query n) (radii : List ℚ≥0)
    (i : ℕ) (hi : i<radii.length) (hb : RegionQueryHeight.Bounds (atRadius q radii[i]) H)
    (hB : 2*(2^H)^2+3 < B) (hindex : 2*(n*n)+2 < B) (hvertex : 2*n+2 < B)
    (hposition : 2*i+1 < B) :
    Spec B (fun σ => Context q radii σ ∧ σ.vars "find.i"=i) test
      (fun _ τ => Context q radii τ ∧ τ.vars "find.ok" = if predicate q radii i then 1 else 0)
      (queryCost n H+18) := by
  rintro σ hσ
  obtain ⟨τ,rr,pr⟩ := test_answer_spec B H q radii i hi hb hB hindex hvertex hposition σ hσ
  refine ⟨τ,rr,pr.1,?_⟩
  simpa only [RadiusSearchData.predicate,List.getD_eq_get radii 0 (⟨i,hi⟩ : Fin radii.length),List.get_eq_getElem] using pr.2.2.2.2.2.2.2

theorem setFinder {n : ℕ} {q : Query n} {radii : List ℚ≥0} {σ : Env}
    (h : Context q radii σ) (k : ℕ) (name : String)
    (hname : name ∈ ["find.i","find.found","find.result"]) : Context q radii (σ.setVar name k) := by
  obtain ⟨r,hr⟩ := h.input
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hname
  rcases hname with rfl|rfl|rfl
  all_goals
    refine ⟨⟨r,?_⟩,?_,?_,?_,?_,?_⟩
  all_goals first
    | exact (by simpa only [Prefix,arrs_setVar] using h.radiusData)
    | exact (by simpa only [vars_setVar,String.reduceEq,if_false] using h.count)
    | exact (by simpa only [arrs_setVar] using h.outRoom)
    | exact (by simpa only [arrs_setVar] using h.inRoom)
    | exact (by simpa only [arrs_setVar] using h.crossingRoom)
    | (refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
       all_goals first
         | exact (by simpa only [vars_setVar,String.reduceEq,if_false] using hr.nValue)
         | exact (by simpa only [vars_setVar,String.reduceEq,if_false] using hr.n2Value)
         | exact (by simpa only [Stored,String.reduceAppend,vars_setVar,String.reduceEq,if_false] using hr.radiusData)
         | exact (by simpa only [Stored,String.reduceAppend,vars_setVar,String.reduceEq,if_false] using hr.seedData)
         | exact (by simpa only [Stored,String.reduceAppend,vars_setVar,String.reduceEq,if_false] using hr.betaData)
         | exact (by simpa only [Prefix,arrs_setVar] using hr.weightsData)
         | exact (by simpa only [Prefix,arrs_setVar] using hr.capacityData)
         | exact (by simpa only [Prefix,arrs_setVar] using hr.lengthData)
         | exact (by simpa only [Prefix,arrs_setVar] using hr.outData)
         | exact (by simpa only [Prefix,arrs_setVar] using hr.inData))

def command : Com := RamFind.command test

set_option maxHeartbeats 2400000 in
/-- A single fixed native search examines candidate radii in buffer order and
records exactly the first successful region query. It also terminates when
no candidate succeeds. -/
theorem command_spec (B H : ℕ) {n : ℕ} (q : Query n) (radii : List ℚ≥0)
    (hb : ∀ i, ∀ hi : i<radii.length, RegionQueryHeight.Bounds (atRadius q radii[i]) H)
    (hB : 2*(2^H)^2+3 < B) (hindex : 2*(n*n)+2 < B) (hvertex : 2*n+2 < B)
    (hposition : 2*radii.length+2 < B) :
    Spec B (Context q radii) command
      (fun _ τ => Context q radii τ ∧ RamFind.Matches
        (RamFind.first (predicate q radii) radii.length) τ)
      ((queryCost n H+38)*radii.length+10) := by
  apply RamFind.command_spec B radii.length (queryCost n H+18) (Context q radii) (predicate q radii) test
    (by omega) (by omega) (fun _ h => h.count) (fun _ k name h hn => setFinder h k name hn)
  · intro i hi
    exact test_spec B H q radii i hi (hb i hi) hB hindex hvertex (by omega)
  · decide

end Lax455465Proofs.RamRadiusSearch
