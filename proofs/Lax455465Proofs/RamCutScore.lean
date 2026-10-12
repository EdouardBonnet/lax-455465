import Lax455465Proofs.RamCutRatio

namespace Lax455465Proofs.RamCutScore
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar
open Lax455465.RationalEncoding CutScoreData
open scoped NNRat

def command : Com := .seq RamCutMeasures.command RamCutRatio.command

def cost (n M : ℕ) : ℕ := (36*(M^2).size+234)*(n*n)+(36*(M^2).size+152)*n+144*(M^2).size+468

set_option maxHeartbeats 2400000 in
/-- One fixed native shore-scoring command computes the exact sparsity
ratio and admissibility flag from the original graph and current membership
buffer. The source buffers and current shore are preserved. -/
theorem command_spec (B M : ℕ) {n : ℕ} (I : RationalInstance n) (S : Finset (Fin n)) (hM : 1≤M)
    (hb : CutScoreHeight.Bounds I S M) (hB : 2*M^2+3<B) (hindex : 2*(n*n)+2<B) (hvertex : 2*n+2<B) :
    Spec B (fun σ => RamCutMeasures.Input I S σ ∧ 2*(n*n)<(σ.arrs "cut.crossing").length) command
      (fun _ τ => RamCutMeasures.Input I S τ ∧ Stored "cut.ratio" (ratio I S) τ ∧
        τ.vars "cut.valid"=if CutSweeps.admissibleQ I S then 1 else 0) (cost n M) := by
  rintro σ hσ
  obtain ⟨ν,rm,pm⟩ := RamCutMeasures.command_spec B M I S hM hb hB hindex hvertex σ hσ
  obtain ⟨τ,rr,pr⟩ := RamCutRatio.command_spec B M I S hM hb hB ν
    ⟨pm.1.totalData,pm.2.1,pm.2.2⟩
  refine ⟨τ,(rm.seq rr).mono (by dsimp [cost]; omega),?_,pr.2.2.2.1,pr.2.2.2.2⟩
  exact ⟨(rr.frame_var _ (by decide)).trans pm.1.nValue,(rr.frame_var _ (by decide)).trans pm.1.n2Value,
    pr.1.totalData,
    by simpa only [Prefix,rr.frame_arr "flow.weights" (by decide)] using pm.1.weightsData,
    by simpa only [Prefix,rr.frame_arr "flow.capacities" (by decide)] using pm.1.capacityData,
    by simpa only [Prefix,rr.frame_arr "cut.flags" (by decide)] using pm.1.maskData⟩

end Lax455465Proofs.RamCutScore
