import Lax455465Proofs.RadiusLookup
import Lax455465Proofs.RamGridRadius
import Lax455465Proofs.RamEventRadius

namespace Lax455465Proofs.RamRadiusCoefficient

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamUnsignedScalar RamRational RamVirtualState
open scoped NNRat

structure Source {n : ℕ} (outDistance inDistance : Fin n → ℚ≥0) (k : ℕ) (delta : ℚ≥0) (σ : Env) : Prop where
  nValue : σ.vars "metric.n"=n
  kValue : σ.vars "round.steps"=k
  deltaData : Stored "round.delta" delta σ
  unitData : Stored "round.gridStep" (delta/(k : ℚ≥0)) σ
  outData : Prefix (RamUnsignedBuffer.encode (List.ofFn outDistance)) "region.out" σ
  inData : Prefix (RamUnsignedBuffer.encode (List.ofFn inDistance)) "region.in" σ

structure Context {n : ℕ} (outDistance inDistance : Fin n → ℚ≥0) (k : ℕ) (delta : ℚ≥0) (σ : Env) : Prop where
  source : Source outDistance inDistance k delta σ
  gridCount : σ.vars "radius.gridCount"=k+1
  count : σ.vars "radius.count"=k+1+2*n

def names : List String := ["metric.n","round.steps","round.delta.n","round.delta.d","round.gridStep.n","round.gridStep.d","radius.gridCount","radius.count"]
def arrays : List String := ["region.out","region.in"]

theorem frame {B K : ℕ} {cmd : Com} {σ τ : Env} (hr : Run B cmd σ τ K)
    {n : ℕ} {outDistance inDistance : Fin n → ℚ≥0} {k : ℕ} {delta : ℚ≥0}
    (h : Context outDistance inDistance k delta σ)
    (hx : ∀ x ∈ names, x ∉ cmd.wvars) (ha : ∀ a ∈ arrays, a ∉ cmd.warrs) :
    Context outDistance inDistance k delta τ := by
  refine ⟨⟨(hr.frame_var _ (hx _ (by simp [names]))).trans h.source.nValue,
    (hr.frame_var _ (hx _ (by simp [names]))).trans h.source.kValue,?_,?_,?_,?_⟩,
    (hr.frame_var _ (hx _ (by simp [names]))).trans h.gridCount,
    (hr.frame_var _ (hx _ (by simp [names]))).trans h.count⟩
  · simpa only [Stored,String.reduceAppend,hr.frame_var "round.delta.n" (hx _ (by simp [names])),hr.frame_var "round.delta.d" (hx _ (by simp [names]))] using h.source.deltaData
  · simpa only [Stored,String.reduceAppend,hr.frame_var "round.gridStep.n" (hx _ (by simp [names])),hr.frame_var "round.gridStep.d" (hx _ (by simp [names]))] using h.source.unitData
  · simpa only [Prefix,hr.frame_arr "region.out" (ha _ (by simp [arrays]))] using h.source.outData
  · simpa only [Prefix,hr.frame_arr "region.in" (ha _ (by simp [arrays]))] using h.source.inData

def vertex : Com := .seq (.assign "radius.v" (.sub (.var "radius.i") (.var "radius.gridCount")))
  (.ite (.lt (.var "radius.v") (.var "metric.n")) (RamEventRadius.command true)
    (.seq (.assign "radius.v" (.sub (.var "radius.v") (.var "metric.n"))) (RamEventRadius.command false)))

def command : Com := .ite (.lt (.var "radius.i") (.var "radius.gridCount")) RamGridRadius.command vertex

set_option maxHeartbeats 1600000 in
/-- Generate the next candidate from its runtime position: rational grid,
clipped outward event, or clipped inward event. No event sorting occurs. -/
theorem command_spec (B M : ℕ) {n : ℕ} (outDistance inDistance : Fin n → ℚ≥0) (k : ℕ) (delta : ℚ≥0)
    (i : ℕ) (hi : i<k+1+2*n) (hk : k≤M) (hB : 2*M^2+3 < B) (hcount : k+1+2*n+2 < B)
    (hun : (delta/(k : ℚ≥0)).num ≤ M) (hud : (delta/(k : ℚ≥0)).den ≤ M)
    (hdn : delta.num ≤ M) (hdd : delta.den ≤ M)
    (hon : ∀ v, (outDistance v).num ≤ M) (hod : ∀ v, (outDistance v).den ≤ M)
    (hin : ∀ v, (inDistance v).num ≤ M) (hid : ∀ v, (inDistance v).den ≤ M) :
    Spec B (fun σ => Context outDistance inDistance k delta σ ∧ σ.vars "radius.i"=i)
      command (fun _ τ => Context outDistance inDistance k delta τ ∧
        FractionOutput (((RadiusData.candidates outDistance inDistance k delta)[i]'(by rw [RadiusData.length_candidates]; exact hi) : ℚ≥0) : ℚ) τ)
      (36*(M^2).size+100) := by
  have hM1 : 1≤M := (delta/(k : ℚ≥0)).den_pos.trans_le hud
  have hiB : i<B := by omega
  have hnB : n<B := by omega
  have hgB : k+1<B := by omega
  rintro σ ⟨hctx,hidx⟩
  have hc : (Cond.lt (.var "radius.i") (.var "radius.gridCount")).evalB B σ = some (decide (i<k+1)) := by
    rw [evalB_condLt (evalB_var (hidx ▸ hiB)) (evalB_var (hctx.gridCount ▸ hgB)),hidx,hctx.gridCount]
  by_cases hg : i<k+1
  · obtain ⟨τ,rg,pg⟩ := RamGridRadius.command_spec B M i (delta/(k : ℚ≥0)) hB hun hud (by omega) σ ⟨hctx.source.unitData,hidx⟩
    have rr := Run.ite_true (d := vertex) (by simpa only [hg,decide_true] using hc) rg
    refine ⟨τ,rr.mono ?_,frame rg hctx (by dsimp [names]; decide) (by dsimp [arrays]; decide),?_⟩
    · have hsize : (delta/(k : ℚ≥0)).den.size ≤ (M^2).size := Nat.size_le_size (by nlinarith [hud])
      dsimp only [Cond.size,Expr.size]; omega
    · simpa only [RadiusLookup.grid_at outDistance inDistance k delta i hg] using pg
  · let j := i-(k+1)
    let ν := σ.setVar "radius.v" j
    have rj : Run B (.assign "radius.v" (.sub (.var "radius.i") (.var "radius.gridCount"))) σ ν 4 :=
      Run.assign (evalB_bin (op := .sub) (m := i) (n := k+1)
        (by rw [evalB_var_iff]; exact ⟨hidx.symm,hidx ▸ hiB⟩)
        (by rw [evalB_var_iff]; exact ⟨hctx.gridCount.symm,hctx.gridCount ▸ hgB⟩) (by dsimp [Bop.apply]; omega))
    have hctxν := frame rj hctx (by dsimp [names]; decide) (by dsimp [arrays]; decide)
    have hj : j<2*n := by dsimp [j]; omega
    have hjB : j<B := by omega
    have hv : ν.vars "radius.v"=j := by simp [ν]
    have hcv : (Cond.lt (.var "radius.v") (.var "metric.n")).evalB B ν = some (decide (j<n)) := by
      rw [evalB_condLt (evalB_var (hv ▸ hjB)) (evalB_var (hctxν.source.nValue ▸ hnB)),hv,hctxν.source.nValue]
    by_cases ho : j<n
    · let v : Fin n := ⟨j,ho⟩
      obtain ⟨τ,re,pe⟩ := RamEventRadius.command_spec B M true outDistance delta v hB (by omega) hdn hdd (hon v) (hod v) ν
        ⟨hctxν.source.deltaData,hctxν.source.outData,hv⟩
      have rv := rj.seq (Run.ite_true (d := .seq (.assign "radius.v" (.sub (.var "radius.v") (.var "metric.n"))) (RamEventRadius.command false)) (by simpa only [ho,decide_true] using hcv) re)
      have rr := Run.ite_false (c := RamGridRadius.command) (by simpa only [hg,decide_false] using hc) rv
      refine ⟨τ,rr.mono (by dsimp [Cond.size,Expr.size]; omega),frame re hctxν (by dsimp [names]; decide) (by dsimp [arrays]; decide),?_⟩
      have he : i=k+1+v.val := by dsimp [v,j]; omega
      simpa only [he,RadiusLookup.out_at] using pe
    · let v : Fin n := ⟨j-n,by omega⟩
      let μ := ν.setVar "radius.v" v.val
      have rshift : Run B (.assign "radius.v" (.sub (.var "radius.v") (.var "metric.n"))) ν μ 4 :=
        Run.assign (evalB_bin (op := .sub) (m := j) (n := n)
          (by rw [evalB_var_iff]; exact ⟨hv.symm,hv ▸ hjB⟩)
          (by rw [evalB_var_iff]; exact ⟨hctxν.source.nValue.symm,hctxν.source.nValue ▸ hnB⟩) (by dsimp [Bop.apply]; omega))
      have hctxμ := frame rshift hctxν (by dsimp [names]; decide) (by dsimp [arrays]; decide)
      obtain ⟨τ,re,pe⟩ := RamEventRadius.command_spec B M false inDistance delta v hB (by omega) hdn hdd (hin v) (hid v) μ
        ⟨hctxμ.source.deltaData,hctxμ.source.inData,by simp [μ]⟩
      have rv := rj.seq (Run.ite_false (c := RamEventRadius.command true) (by simpa only [ho,decide_false] using hcv) (rshift.seq re))
      have rr := Run.ite_false (c := RamGridRadius.command) (by simpa only [hg,decide_false] using hc) rv
      refine ⟨τ,rr.mono (by dsimp [Cond.size,Expr.size]; omega),frame re hctxμ (by dsimp [names]; decide) (by dsimp [arrays]; decide),?_⟩
      have he : i=k+1+n+v.val := by dsimp [v,j]; omega
      simpa only [he,RadiusLookup.in_at] using pe

end Lax455465Proofs.RamRadiusCoefficient
