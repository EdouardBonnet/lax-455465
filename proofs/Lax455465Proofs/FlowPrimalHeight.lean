import Lax455465Proofs.FlowDistanceBounds

namespace Lax455465Proofs.FlowPrimalHeight
open Lax455465.RationalEncoding Lax455465.ProductNetwork DirectedFlowLP
open Lax759944.BinaryWordEncoding Lax759944.RamPolytime

noncomputable def bound (sourceWord : Polynomial ℕ) : Polynomial ℕ := sourceWord.comp LpInputSize.sizeBound

theorem polynomial_height (sourceWord : Polynomial ℕ) {n : ℕ} (kind : EdgeKind)
    (I : RationalInstance n) (z : Fin (RamFlowData.columns n) → ℚ) (y : Fin (RamFlowData.rows n) → ℚ)
    (hfit : FitsInWords (sourceWord.eval (bitSize (Lax109476.RationalEncoding.encodeProgram (program I))))
      (Lax109476.RationalEncoding.encodeCertificate (.optimal z y))) :
    ∀ i,LpInputSize.Height (2^((bound sourceWord).eval (bitSize (encodeInput kind I)))) (z i) := by
  have hzfit : FitsInWords (sourceWord.eval (bitSize (Lax109476.RationalEncoding.encodeProgram (program I))))
      (Lax109476.RationalEncoding.encodeVector z) := by
    intro word hw
    exact hfit word (by
      simp only [Lax109476.RationalEncoding.encodeCertificate,List.mem_append]
      exact Or.inl (Or.inr hw))
  have hs := LpInputSize.flow_program_polynomial_size kind I
  intro i
  apply LpInputSize.height_mono (FlowDistanceBounds.vector_height _ z hzfit i)
  apply Nat.pow_le_pow_right (by decide)
  simpa only [bound,Polynomial.eval_comp] using RamFlowSolverBounds.eval_mono sourceWord hs

end Lax455465Proofs.FlowPrimalHeight
