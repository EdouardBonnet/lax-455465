import Lax455465Proofs.RamRadiusCoefficient
import Lax455465Proofs.RamUnsignedVector

namespace Lax455465Proofs.RamRadiusCandidates

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamUnsignedScalar RamVirtualState RamRational RamRadiusCoefficient
open scoped NNRat

def setup : Com := .seq (.assign "radius.gridCount" (.add (.var "round.steps") (.lit 1)))
  (.seq (.assign "radius.count" (.add (.var "radius.gridCount") (.mul (.lit 2) (.var "metric.n"))))
    (.assign "radius.position" (.lit 0)))

def command : Com := .seq setup (RamUnsignedVector.command "radius.i" "radius.count" "region.radii" "radius.position" RamRadiusCoefficient.command)

set_option maxHeartbeats 1600000 in
/-- Emit the complete exact radius buffer in the order used by mathematical
region search. The graph order and grid budget are read from runtime data. -/
theorem command_spec (B M : ℕ) {n : ℕ} (outDistance inDistance : Fin n → ℚ≥0) (k : ℕ) (delta : ℚ≥0)
    (hk : k≤M) (hB : 2*M^2+3 < B) (hindex : 2*(k+1+2*n)+2 < B)
    (hun : (delta/(k : ℚ≥0)).num ≤ M) (hud : (delta/(k : ℚ≥0)).den ≤ M)
    (hdn : delta.num ≤ M) (hdd : delta.den ≤ M)
    (hon : ∀ v, (outDistance v).num ≤ M) (hod : ∀ v, (outDistance v).den ≤ M)
    (hin : ∀ v, (inDistance v).num ≤ M) (hid : ∀ v, (inDistance v).den ≤ M) :
    Spec B (fun σ => Source outDistance inDistance k delta σ ∧
      2*(k+1+2*n) < (σ.arrs "region.radii").length) command
      (fun _ τ => Context outDistance inDistance k delta τ ∧
        Prefix (RamUnsignedBuffer.encode (RadiusData.candidates outDistance inDistance k delta)) "region.radii" τ)
      ((36*(M^2).size+122)*(k+1+2*n)+18) := by
  have hM1 : 1≤M := (delta/(k : ℚ≥0)).den_pos.trans_le hud
  have h2 : 2<B := by nlinarith
  have hnB : n<B := by omega
  have hkB : k<B := by omega
  have hgB : k+1<B := by omega
  have htB : k+1+2*n<B := by omega
  have hmB : M*M<B := by nlinarith
  let qs := RadiusData.candidates outDistance inDistance k delta
  have hlen : qs.length=k+1+2*n := RadiusData.length_candidates _ _ _ _
  have hheight : ∀ q ∈ qs, LpInputSize.Height (M*M) (q : ℚ) := by
    apply RadiusData.height outDistance inDistance k M delta hM1 hk
    · exact ⟨by simpa only [NNRat.natAbs_num_coe] using hun,by simpa only [NNRat.den_coe] using hud⟩
    · exact ⟨by simpa only [NNRat.natAbs_num_coe] using hdn,by simpa only [NNRat.den_coe] using hdd⟩
    · intro v; exact ⟨by simpa only [NNRat.natAbs_num_coe] using hon v,by simpa only [NNRat.den_coe] using hod v⟩
    · intro v; exact ⟨by simpa only [NNRat.natAbs_num_coe] using hin v,by simpa only [NNRat.den_coe] using hid v⟩
  have hwords : ∀ i, ∀ hi : i<qs.length, qs[i].num<B ∧ qs[i].den<B := by
    intro i hi
    have hh := hheight qs[i] (List.getElem_mem hi)
    exact ⟨(show qs[i].num≤M*M by simpa only [NNRat.natAbs_num_coe] using hh.1).trans_lt hmB,
      (show qs[i].den≤M*M by simpa only [NNRat.den_coe] using hh.2).trans_lt hmB⟩
  have hf := RamUnsignedVector.command_spec B (36*(M^2).size+100) (Context outDistance inDistance k delta)
    "radius.i" "radius.count" "region.radii" "radius.position" qs [] RamRadiusCoefficient.command (by omega)
    (by simp only [List.length_nil,hlen]; omega)
    (fun i hi => (hwords i hi).1) (fun i hi => (hwords i hi).2)
    (fun _ h => by simpa only [hlen] using h.count)
    (fun σ j h => by
      refine ⟨⟨?_,?_,?_,?_,?_,?_⟩,?_,?_⟩
      all_goals simpa only [Source,Context,Stored,Prefix,vars_setVar,arrs_setVar,String.reduceAppend,String.reduceEq,if_false] using
        (by first | exact h.source.nValue | exact h.source.kValue | exact h.source.deltaData | exact h.source.unitData | exact h.source.outData | exact h.source.inData | exact h.gridCount | exact h.count))
    (fun i hi => RamRadiusCoefficient.command_spec B M outDistance inDistance k delta i (by rwa [hlen] at hi) hk hB (by omega) hun hud hdn hdd hon hod hin hid)
    (by decide) (by decide) (by decide) (by decide)
    (fun rr h => frame rr h (by dsimp [names]; decide) (by dsimp [arrays]; decide)) (by decide) (by decide)
  rintro σ ⟨hsource,hroom⟩
  let σ₁ := σ.setVar "radius.gridCount" (k+1)
  let σ₂ := σ₁.setVar "radius.count" (k+1+2*n)
  let ν := σ₂.setVar "radius.position" 0
  have rgrid : Run B (.assign "radius.gridCount" (.add (.var "round.steps") (.lit 1))) σ σ₁ 4 :=
    Run.assign (evalB_bin (op := .add) (m := k) (n := 1)
      (by rw [evalB_var_iff]; exact ⟨hsource.kValue.symm,hsource.kValue ▸ hkB⟩) (evalB_lit (by omega)) (by dsimp [Bop.apply]; omega))
  have rnσ₁ : σ₁.vars "metric.n"=n := by simpa only [σ₁,vars_setVar,String.reduceEq,if_false] using hsource.nValue
  have rcount : Run B (.assign "radius.count" (.add (.var "radius.gridCount") (.mul (.lit 2) (.var "metric.n")))) σ₁ σ₂ 6 :=
    Run.assign (evalB_bin (op := .add) (m := k+1) (n := 2*n)
      (by rw [evalB_var_iff]; exact ⟨by simp [σ₁],by simpa only [σ₁,vars_setVar,if_true] using hgB⟩)
      (evalB_bin (op := .mul) (m := 2) (n := n) (evalB_lit h2)
        (by rw [evalB_var_iff]; exact ⟨rnσ₁.symm,rnσ₁ ▸ hnB⟩) (by dsimp [Bop.apply]; omega)) (by dsimp [Bop.apply]; exact htB))
  have rpos : Run B (.assign "radius.position" (.lit 0)) σ₂ ν 2 := Run.assign (evalB_lit (by omega))
  have hctxν : Context outDistance inDistance k delta ν := by
    refine ⟨⟨?_,?_,?_,?_,?_,?_⟩,?_,?_⟩
    · simpa only [ν,σ₂,σ₁,vars_setVar,String.reduceEq,if_false] using hsource.nValue
    · simpa only [ν,σ₂,σ₁,vars_setVar,String.reduceEq,if_false] using hsource.kValue
    · simpa only [Stored,ν,σ₂,σ₁,vars_setVar,String.reduceAppend,String.reduceEq,if_false] using hsource.deltaData
    · simpa only [Stored,ν,σ₂,σ₁,vars_setVar,String.reduceAppend,String.reduceEq,if_false] using hsource.unitData
    · simpa only [Prefix,ν,σ₂,σ₁,arrs_setVar] using hsource.outData
    · simpa only [Prefix,ν,σ₂,σ₁,arrs_setVar] using hsource.inData
    · simp [ν,σ₂,σ₁]
    · simp [ν,σ₂]
  obtain ⟨τ,rr,pr⟩ := hf ν ⟨hctxν,by intro i hi; simp at hi,by simp [ν],
    by simpa only [ν,σ₂,σ₁,arrs_setVar,List.length_nil,Nat.zero_add,hlen] using hroom⟩
  exact ⟨τ,((rgrid.seq (rcount.seq rpos)).seq rr).mono (by simp only [hlen,Nat.add_assoc,Nat.reduceAdd]; omega),pr.1,by simpa only [List.nil_append,qs] using pr.2.1⟩

end Lax455465Proofs.RamRadiusCandidates
