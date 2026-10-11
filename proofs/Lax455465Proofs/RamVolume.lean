import Lax455465Proofs.RamVolumeCoefficient
import Lax455465Proofs.RamUnsignedSum

namespace Lax455465Proofs.RamVolume

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamVirtualState RamUnsignedScalar MetricMatrix
open scoped NNRat

def Context {n : ℕ} (outward : Bool) (capacity length : Matrix n) (distance : Fin n → ℚ≥0)
    (seed radius : ℚ≥0) (σ : Env) : Prop :=
  σ.vars "metric.n" = n ∧ σ.vars "metric.n2" = n*n ∧ Stored "region.radius" radius σ ∧
    Stored "round.seed" seed σ ∧ Prefix (RamUnsignedBuffer.encode (values capacity)) "region.capacities" σ ∧
    Prefix (RamUnsignedBuffer.encode (values length)) "metric.old" σ ∧
    Prefix (RamUnsignedBuffer.encode (List.ofFn distance)) (RamRootDistances.array outward) σ

def SumContext {n : ℕ} (outward : Bool) (capacity length : Matrix n) (distance : Fin n → ℚ≥0)
    (seed radius : ℚ≥0) (σ : Env) : Prop :=
  RamVolumeCoefficient.Context outward capacity length distance radius σ ∧
    σ.vars "sum.count" = n*n ∧ Stored "round.seed" seed σ

def setup : Com := .seq (load "region.radius") (.seq (save "portion.radius") (.assign "sum.count" (.var "metric.n2")))
def sum (outward : Bool) : Com := RamUnsignedSum.command "sum.i" "sum.count" (RamVolumeCoefficient.command outward)
def addition : Com := RamScalarBinary.command "round.seed" "volume.sum" addFraction

def command (outward : Bool) : Com := .seq setup (.seq (sum outward)
  (.seq (save "volume.sum") (.seq addition (save "region.volume"))))

set_option maxHeartbeats 2400000 in
/-- Evaluate the exact seeded rational volume. Every coefficient and every
partial sum is connected to the native execution and its instruction bound. -/
theorem command_spec (B M : ℕ) {n : ℕ} (outward : Bool) (capacity length : Matrix n)
    (distance : Fin n → ℚ≥0) (seed radius : ℚ≥0) (hB : 2*M^2+3 < B)
    (hindex : 2*(n*n)+2 < B) (hvertex : 2*n+2 < B)
    (hcn : ∀ u v, (capacity u v).num ≤ M) (hcd : ∀ u v, (capacity u v).den ≤ M)
    (hln : ∀ u v, (length u v).num ≤ M) (hld : ∀ u v, (length u v).den ≤ M)
    (hdn : ∀ v, (distance v).num ≤ M) (hdd : ∀ v, (distance v).den ≤ M)
    (hsn : seed.num ≤ M) (hsd : seed.den ≤ M) (hrn : radius.num ≤ M) (hrd : radius.den ≤ M)
    (htn : ∀ v, (RamTruncatedSubtract.value radius (distance v)).num ≤ M)
    (htd : ∀ v, (RamTruncatedSubtract.value radius (distance v)).den ≤ M)
    (hpn : ∀ u v, (RamEdgePortion.value (length u v) (VolumeData.base outward distance u v) radius).num ≤ M)
    (hpd : ∀ u v, (RamEdgePortion.value (length u v) (VolumeData.base outward distance u v) radius).den ≤ M)
    (hqn : ∀ q ∈ VolumeData.coefficients outward capacity length distance radius, q.num ≤ M)
    (hqd : ∀ q ∈ VolumeData.coefficients outward capacity length distance radius, q.den ≤ M)
    (hprefixNum : ∀ i, ((VolumeData.coefficients outward capacity length distance radius).take i).sum.num ≤ M)
    (hprefixDen : ∀ i, ((VolumeData.coefficients outward capacity length distance radius).take i).sum.den ≤ M)
    (hvn : (VolumeData.value outward capacity length distance seed radius).num ≤ M)
    (hvd : (VolumeData.value outward capacity length distance seed radius).den ≤ M) :
    Spec B (Context outward capacity length distance seed radius) (command outward)
      (fun _ τ => Context outward capacity length distance seed radius τ ∧
        Stored "region.volume" (VolumeData.value outward capacity length distance seed radius) τ)
      ((108*(M^2).size+502)*(n*n)+36*(M^2).size+156) := by
  have hM : M < B := by nlinarith
  have h1 : 1 < B := by nlinarith
  let qs := VolumeData.coefficients outward capacity length distance radius
  have hlen : qs.length = n*n := length_values _
  have hfinalN : qs.sum.num ≤ M := by simpa only [qs,List.take_length] using hprefixNum qs.length
  have hfinalD : qs.sum.den ≤ M := by simpa only [qs,List.take_length] using hprefixDen qs.length
  have hbody : ∀ i, ∀ hi : i < qs.length,
      Spec B (fun σ => SumContext outward capacity length distance seed radius σ ∧ σ.vars "sum.i"=i)
        (RamVolumeCoefficient.command outward)
        (fun _ τ => SumContext outward capacity length distance seed radius τ ∧ FractionOutput (qs[i] : ℚ) τ)
        (72*(M^2).size+382) := by
    intro i hi σ hσ
    have he : i < n*n := by rwa [hlen] at hi
    let uv := (DirectedFlowLP.edgeIndex n).symm (⟨i,he⟩ : Fin (n*n))
    have hidx : DirectedFlowLP.edgeIndex n uv = (⟨i,he⟩ : Fin (n*n)) := (DirectedFlowLP.edgeIndex n).apply_symm_apply _
    have hdn' : (VolumeData.base outward distance uv.1 uv.2).num ≤ M := by cases outward <;> exact hdn _
    have hdd' : (VolumeData.base outward distance uv.1 uv.2).den ≤ M := by cases outward <;> exact hdd _
    have htn' : (RamTruncatedSubtract.value radius (VolumeData.base outward distance uv.1 uv.2)).num ≤ M := by cases outward <;> exact htn _
    have htd' : (RamTruncatedSubtract.value radius (VolumeData.base outward distance uv.1 uv.2)).den ≤ M := by cases outward <;> exact htd _
    obtain ⟨τ,rr,pr⟩ := RamVolumeCoefficient.command_spec B M outward capacity length distance radius uv.1 uv.2 hB
      (by omega) (by omega) hindex hvertex (hcn _ _) (hcd _ _) (hln _ _) (hld _ _)
      hdn' hdd' hrn hrd htn' htd' (hpn _ _) (hpd _ _) σ ⟨hσ.1.1,by simpa only [hidx] using hσ.2⟩
    refine ⟨τ,rr,⟨pr.1,?_,?_⟩,?_⟩
    · exact (rr.frame_var "sum.count" (by cases outward <;> decide)).trans hσ.1.2.1
    · simpa only [Stored,String.reduceAppend,rr.frame_var "round.seed.n" (by cases outward <;> decide),
        rr.frame_var "round.seed.d" (by cases outward <;> decide)] using hσ.1.2.2
    · simpa only [qs,VolumeData.coefficients,values,List.getElem_ofFn,uv,Fin.eta] using pr.2
  have hset : ∀ σ k name, SumContext outward capacity length distance seed radius σ →
      name="sum.i" ∨ name="fold.n" ∨ name="fold.d" → SumContext outward capacity length distance seed radius (σ.setVar name k) := by
    intro σ k name hσ hname
    rcases hname with rfl|rfl|rfl <;>
      simpa only [SumContext,RamVolumeCoefficient.Context,Stored,Prefix,vars_setVar,arrs_setVar,String.reduceAppend,String.reduceEq,if_false] using hσ
  have hfold := RamUnsignedSum.command_spec B M (72*(M^2).size+382)
    (SumContext outward capacity length distance seed radius) "sum.i" "sum.count" qs (RamVolumeCoefficient.command outward)
    hB (by omega) hqn hqd hprefixNum hprefixDen (fun _ h => by simpa only [hlen] using h.2.1)
    hset hbody (by decide) (by cases outward <;> decide) (by cases outward <;> decide)
    (fun rr h => by
      simpa only [SumContext,RamVolumeCoefficient.Context,Stored,Prefix,String.reduceAppend,
        rr.frame_var "metric.n" (by decide),rr.frame_var "metric.n2" (by decide),rr.frame_var "portion.radius.n" (by decide),
        rr.frame_var "portion.radius.d" (by decide),rr.frame_var "sum.count" (by decide),
        rr.frame_var "round.seed.n" (by decide),rr.frame_var "round.seed.d" (by decide),
        rr.frame_arr "region.capacities" (by decide),rr.frame_arr "metric.old" (by decide),
        rr.frame_arr (RamRootDistances.array outward) (by change RamRootDistances.array outward ∉ ([] : List String); simp)] using h)
    (fun rr h => by
      simpa only [SumContext,RamVolumeCoefficient.Context,Stored,Prefix,String.reduceAppend,
        rr.frame_var "metric.n" (by decide),rr.frame_var "metric.n2" (by decide),rr.frame_var "portion.radius.n" (by decide),
        rr.frame_var "portion.radius.d" (by decide),rr.frame_var "sum.count" (by decide),
        rr.frame_var "round.seed.n" (by decide),rr.frame_var "round.seed.d" (by decide),
        rr.frame_arr "region.capacities" (by decide),rr.frame_arr "metric.old" (by decide),
        rr.frame_arr (RamRootDistances.array outward) (by change RamRootDistances.array outward ∉ ([] : List String); simp)] using h)
  intro σ hctx
  obtain ⟨σ₁,r₁,p₁⟩ := load_spec B "region.radius" radius h1 (hrn.trans_lt hM) (hrd.trans_lt hM) (by decide) σ hctx.2.2.1
  obtain ⟨σ₂,r₂,p₂⟩ := save_spec B "portion.radius" radius (hrn.trans_lt hM) (hrd.trans_lt hM) (by decide) σ₁ p₁
  have hn2₂ : σ₂.vars "metric.n2"=n*n := by
    have rr := r₁.seq r₂
    exact (rr.frame_var _ (by decide)).trans hctx.2.1
  let σ₃ := σ₂.setVar "sum.count" (n*n)
  have r₃ : Run B (.assign "sum.count" (.var "metric.n2")) σ₂ σ₃ 2 :=
    Run.assign (by rw [evalB_var_iff]; exact ⟨hn2₂.symm,hn2₂ ▸ (by omega : n*n < B)⟩)
  have rsetup := r₁.seq (r₂.seq r₃)
  have hsumCtx : SumContext outward capacity length distance seed radius σ₃ := by
    refine ⟨⟨?_,?_,?_,?_,?_,?_⟩,by simp [σ₃],?_⟩
    · exact (rsetup.frame_var _ (by decide)).trans hctx.1
    · exact (rsetup.frame_var _ (by decide)).trans hctx.2.1
    · simpa only [Stored,String.reduceAppend,r₃.frame_var "portion.radius.n" (by decide),r₃.frame_var "portion.radius.d" (by decide)] using p₂
    · simpa only [Prefix,rsetup.frame_arr "region.capacities" (by decide)] using hctx.2.2.2.2.1
    · simpa only [Prefix,rsetup.frame_arr "metric.old" (by decide)] using hctx.2.2.2.2.2.1
    · simpa only [Prefix,rsetup.frame_arr (RamRootDistances.array outward) (by change RamRootDistances.array outward ∉ ([] : List String); simp)] using hctx.2.2.2.2.2.2
    · simpa only [Stored,String.reduceAppend,rsetup.frame_var "round.seed.n" (by decide),rsetup.frame_var "round.seed.d" (by decide)] using hctx.2.2.2.1
  obtain ⟨σ₄,r₄,p₄⟩ := hfold σ₃ hsumCtx
  obtain ⟨σ₅,r₅,p₅⟩ := save_spec B "volume.sum" qs.sum (hfinalN.trans_lt hM) (hfinalD.trans_lt hM) (by decide) σ₄ p₄.2
  have hseed : Stored "round.seed" seed σ₅ := by
    simpa only [Stored,String.reduceAppend,r₅.frame_var "round.seed.n" (by decide),r₅.frame_var "round.seed.d" (by decide)] using p₄.1.2.2
  obtain ⟨σ₆,r₆,p₆⟩ := RamScalarBinary.command_spec B M (36*(M^2).size+96) seed qs.sum "round.seed" "volume.sum" addFraction
    ((seed+qs.sum : ℚ≥0) : ℚ) hB hsn hsd hfinalN hfinalD (by decide) (by decide) (by decide)
    (fun σ h => by
      obtain ⟨τ,rr,pr⟩ := RamUnsignedArithmetic.add_spec B M seed qs.sum hB hsn hsd hfinalN hfinalD σ h
      have hcost : (seed.den*qs.sum.den).size ≤ (M^2).size := Nat.size_le_size (by nlinarith [Nat.mul_le_mul hsd hfinalD])
      exact ⟨τ,rr.mono (by omega),pr⟩) σ₅ ⟨hseed,p₅⟩
  obtain ⟨τ,r₇,p₇⟩ := save_spec B "region.volume" (VolumeData.value outward capacity length distance seed radius)
    (hvn.trans_lt hM) (hvd.trans_lt hM) (by decide) σ₆ p₆
  have rr := rsetup.seq (r₄.seq (r₅.seq (r₆.seq r₇)))
  refine ⟨τ,rr.mono ?_,?_,p₇⟩
  · simp only [hlen,Nat.add_assoc]
    ring_nf; omega
  · simpa only [Context,Stored,Prefix,String.reduceAppend,
      rr.frame_var "metric.n" (by cases outward <;> decide),rr.frame_var "metric.n2" (by cases outward <;> decide),
      rr.frame_var "region.radius.n" (by cases outward <;> decide),rr.frame_var "region.radius.d" (by cases outward <;> decide),
      rr.frame_var "round.seed.n" (by cases outward <;> decide),rr.frame_var "round.seed.d" (by cases outward <;> decide),
      rr.frame_arr "region.capacities" (by cases outward <;> decide),rr.frame_arr "metric.old" (by cases outward <;> decide),
      rr.frame_arr (RamRootDistances.array outward) (by cases outward <;> decide)] using hctx

end Lax455465Proofs.RamVolume
