import Lax455465Proofs.BoundaryData
import Lax455465Proofs.RamBallMass

namespace Lax455465Proofs.RamBoundary

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamVirtualState RamUnsignedScalar MetricMatrix
open scoped NNRat

def Context {n : ℕ} (outward : Bool) (capacity : Matrix n) (distance : Fin n → ℚ≥0)
    (radius : ℚ≥0) (σ : Env) : Prop :=
  σ.vars "metric.n" = n ∧ σ.vars "metric.n2" = n*n ∧
    Prefix (RamUnsignedBuffer.encode (values capacity)) "region.capacities" σ ∧
    Prefix (RamUnsignedBuffer.encode (BallMassData.mask distance radius)) (RamBallMass.maskArray outward) σ

def command (outward : Bool) : Com :=
  .seq (RamArcMask.command (some outward) (RamBallMass.maskArray outward) "region.crossing")
    (.seq (.assign "sum.count" (.var "metric.n2"))
      (.seq (RamMaskedSum.command "region.capacities" "region.crossing") (save "region.boundary")))

set_option maxHeartbeats 1600000 in
/-- Sum exactly the residual capacities crossing the actual strict ball,
using original arc orientation for both outward and inward boundaries. -/
theorem command_spec (B M : ℕ) {n : ℕ} (outward : Bool) (capacity : Matrix n)
    (distance : Fin n → ℚ≥0) (radius : ℚ≥0) (hM1 : 1 ≤ M)
    (hB : 2*M^2+3 < B) (hindex : 2*(n*n)+2 < B) (hvertex : 2*n+2 < B)
    (hcn : ∀ u v, (capacity u v).num ≤ M) (hcd : ∀ u v, (capacity u v).den ≤ M)
    (hprefixNum : ∀ i, ((RamMaskedSum.coefficients (values capacity) (values (BoundaryData.arcs outward distance radius))).take i).sum.num ≤ M)
    (hprefixDen : ∀ i, ((RamMaskedSum.coefficients (values capacity) (values (BoundaryData.arcs outward distance radius))).take i).sum.den ≤ M) :
    Spec B (fun σ => Context outward capacity distance radius σ ∧ 2*(n*n) < (σ.arrs "region.crossing").length)
      (command outward) (fun _ τ => Context outward capacity distance radius τ ∧
        Prefix (RamUnsignedBuffer.encode (values (BoundaryData.arcs outward distance radius))) "region.crossing" τ ∧
        Stored "region.boundary" (BoundaryData.value outward capacity distance radius) τ)
      ((36*(M^2).size+234)*(n*n)+30) := by
  have hM : M < B := by nlinarith
  have h2 : 2 < B := by nlinarith
  let cs := values capacity
  let ms := values (BoundaryData.arcs outward distance radius)
  have hcLen : cs.length = n*n := length_values _
  have hmLen : ms.length = n*n := length_values _
  have hcN : ∀ q ∈ cs, q.num ≤ M := by
    intro q hq
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq
    exact hcn _ _
  have hcD : ∀ q ∈ cs, q.den ≤ M := by
    intro q hq
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq
    exact hcd _ _
  have hmN : ∀ q ∈ ms, q.num ≤ M := by
    intro q hq
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq
    dsimp only [BoundaryData.arcs,RamArcMask.matrix]
    cases RamBooleanArithmetic.flag (some outward) (BoundaryData.vertices distance radius _) (BoundaryData.vertices distance radius _) <;>
      simp [RamBooleanArithmetic.bit] <;> omega
  have hmD : ∀ q ∈ ms, q.den ≤ M := by
    intro q hq
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq
    dsimp only [BoundaryData.arcs,RamArcMask.matrix]
    cases RamBooleanArithmetic.flag (some outward) (BoundaryData.vertices distance radius _) (BoundaryData.vertices distance radius _) <;>
      simp [RamBooleanArithmetic.bit] <;> omega
  have hfinal : (BoundaryData.value outward capacity distance radius).num ≤ M ∧
      (BoundaryData.value outward capacity distance radius).den ≤ M := by
    simpa only [ms,BoundaryData.value,List.take_length] using
      And.intro (hprefixNum (RamMaskedSum.coefficients (values capacity) ms).length)
        (hprefixDen (RamMaskedSum.coefficients (values capacity) ms).length)
  rintro σ ⟨hctx,hroom⟩
  have haCtx : RamArcMask.Context (RamBallMass.maskArray outward) (BoundaryData.vertices distance radius) σ := by
    refine ⟨hctx.1,hctx.2.1,?_⟩
    change Prefix (RamUnsignedBuffer.encode (MaskedMassData.flags (fun v => decide ((distance v : ℚ) < (radius : ℚ))))) (RamBallMass.maskArray outward) σ
    rw [← BallMassData.mask_eq]
    exact hctx.2.2.2
  obtain ⟨ν,rmask,pmask⟩ := RamArcMask.command_spec B (some outward) (RamBallMass.maskArray outward) "region.crossing"
    (BoundaryData.vertices distance radius) (by cases outward <;> decide) h2 (by omega) (by omega) hindex hvertex σ ⟨haCtx,hroom⟩
  let ξ := ν.setVar "sum.count" (n*n)
  have rcount : Run B (.assign "sum.count" (.var "metric.n2")) ν ξ 2 :=
    Run.assign (by rw [evalB_var_iff]; exact ⟨pmask.1.2.1.symm,pmask.1.2.1 ▸ (by omega : n*n < B)⟩)
  have hsumCtx : RamMaskedSum.Context "region.capacities" "region.crossing" cs ms ξ := by
    refine ⟨by simp [ξ,hcLen],?_,?_⟩
    · simpa only [Prefix,ξ,arrs_setVar,cs,rmask.frame_arr "region.capacities" (by cases outward <;> decide)] using hctx.2.2.1
    · simpa only [Prefix,ξ,arrs_setVar,ms,BoundaryData.arcs] using pmask.2
  obtain ⟨μ,rsum,psum⟩ := RamMaskedSum.command_spec B M "region.capacities" "region.crossing" cs ms
    (by omega) hB (by rwa [hcLen]) hcN hcD hmN hmD hprefixNum hprefixDen ξ hsumCtx
  obtain ⟨τ,rsave,psave⟩ := save_spec B "region.boundary" (BoundaryData.value outward capacity distance radius)
    (hfinal.1.trans_lt hM) (hfinal.2.trans_lt hM) (by decide) μ psum.2
  have rr := rmask.seq (rcount.seq (rsum.seq rsave))
  refine ⟨τ,rr.mono ?_,?_,?_,psave⟩
  · simp only [hcLen,Nat.add_assoc,Nat.reduceAdd]
    ring_nf
    omega
  · simpa only [Context,Prefix,
      rr.frame_var "metric.n" (by cases outward <;> decide),
      rr.frame_var "metric.n2" (by cases outward <;> decide),
      rr.frame_arr "region.capacities" (by cases outward <;> decide),
      rr.frame_arr (RamBallMass.maskArray outward) (by cases outward <;> decide)] using hctx
  · have rafter := rcount.seq (rsum.seq rsave)
    simpa only [Prefix,ms,BoundaryData.arcs,rafter.frame_arr "region.crossing" (by decide)] using pmask.2

end Lax455465Proofs.RamBoundary
