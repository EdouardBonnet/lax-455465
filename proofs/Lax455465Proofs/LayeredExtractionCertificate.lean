import Lax455465Proofs.LayeredExtractionState
import Lax455465Proofs.PathCertificateInterpretation

namespace Lax455465Proofs.LayeredExtractionCertificate
open LayeredFlowLP LayeredGraphFlow LayeredWalkState LayeredPathSweep LayeredExtractionLoad
open PathRecordBuffer Lax455465.RationalEncoding Lax455465.ProductNetwork Lax455465.ConcurrentFlow
open Lax455465.ShortPathFlow
open scoped NNRat NNReal

theorem interpretation {n : ℕ} (f : ℚ≥0) (rs : PathRecordBuffer.Records n) :
    PathCertificateInterpretation.certificate (f : ℚ) (rational rs)=⟨f,rs⟩ := by
  simp [PathCertificateInterpretation.certificate,rational,Function.comp_def]

/-- The native extraction invariant yields the public real path-flow
semantics, with the original layered LP's capacities and objective value. -/
theorem correct {n L : ℕ} (I : RationalInstance n) (f : ℚ≥0)
    (q₀ q : Coordinate n L → ℚ≥0) (D H : ℕ) (rs : PathRecordBuffer.Records n)
    (h : LayeredExtractionState.State q₀ (f/2) D H (n*n) q rs)
    (hfeas : LayeredFlowFeasibility.Feasible I (f : ℚ) (arc q₀)) :
    IsConcurrentFlow .undirected I.network (uniformWeight n) (f : ℝ≥0)
      (FlowCertificate.flow ⟨f,rs⟩) ∧ HasPathLengthAtMost (FlowCertificate.flow ⟨f,rs⟩) (L : ℝ) := by
  have hvalid : ∀ r∈rational rs,0≤r.2 ∧ 2≤r.1.length ∧ r.1.Nodup ∧ r.1.length≤L+1 := by
    intro r hr
    obtain ⟨r',hr',rfl⟩:=List.mem_map.mp hr
    have hh:=h.good r' hr'
    exact ⟨r'.2.coe_nonneg,hh.2⟩
  have hcap : ∀ u v,AcyclicFlowDecomposition.load (rational rs) u v+
      AcyclicFlowDecomposition.load (rational rs) v u≤(I.capacity u v : ℚ) := by
    intro u v
    by_cases he : u=v
    · subst v
      have hz := PathRecordArithmetic.load_loop_zero (rational rs) (fun r hr => (hvalid r hr).2.2.1) u
      simp only [hz,add_zero,I.loopless,NNRat.coe_zero,le_refl]
    · have h1:=h.load u v
      have h2:=h.load v u
      have hp1:=nonnegative q u v
      have hp2:=nonnegative q v u
      have hc:=hfeas.2.2.1 (u,v)
      rw [usage_sum q₀ u v he] at hc
      linarith only [h1,h2,hp1,hp2,hc]
  have hdemand : ∀ s t,s≠t → (f : ℚ)/2≤PathRecordArithmetic.routed (rational rs) s t := by
    intro s t hst
    have hi : LayeredExtractionState.index (s,t)<n*n := (DirectedFlowLP.edgeIndex n (s,t)).isLt
    have hh:=h.routed (s,t) hi hst
    rw [hh]
    simp [NNRat.coe_div]
  simpa only [interpretation] using PathCertificateInterpretation.correct (L := L) I (f : ℚ) f.coe_nonneg
    (rational rs) hvalid hcap hdemand

end Lax455465Proofs.LayeredExtractionCertificate
