import Lax455465Proofs.MetricHeight
import Lax455465Proofs.RamFlowSolverBounds
import Lax455465Proofs.RamInputOptimal

namespace Lax455465Proofs.FlowDistanceBounds

open Lax455465.RationalEncoding Lax455465.ProductNetwork DirectedFlowLP
open Lax109476.RationalEncoding Lax109476.RationalCertificates
open Lax759944.RamPolytime Lax759944.BinaryWordEncoding

/-- Bound each exact signed coordinate using its membership in the returned
certificate word. No witness-selection size theorem is substituted here. -/
theorem vector_height (w : ℕ) {k : ℕ} (x : Fin k → ℚ)
    (hwords : FitsInWords w (encodeVector x)) :
    ∀ i, LpInputSize.Height (2^w) (x i) := by
  intro i
  have hn := hwords (x i).num.natAbs (List.mem_flatMap.mpr
    ⟨x i,List.mem_ofFn.mpr ⟨i,rfl⟩,by simp [Lax109476.RationalEncoding.encodeRational]⟩)
  have hd := hwords (x i).den (List.mem_flatMap.mpr
    ⟨x i,List.mem_ofFn.mpr ⟨i,rfl⟩,by simp [Lax109476.RationalEncoding.encodeRational]⟩)
  exact ⟨Nat.le_of_lt hn,Nat.le_of_lt hd⟩

noncomputable def widthBound (sourceWord : Polynomial ℕ) : Polynomial ℕ :=
  sourceWord.comp LpInputSize.sizeBound * (Polynomial.X^2+Polynomial.C 1)

/-- The bit heights of every intermediate shortest-distance matrix are
bounded by a single polynomial in the original graph's binary input size. -/
theorem dual_polynomial_height (sourceWord : Polynomial ℕ) {n : ℕ} (kind : EdgeKind)
    (I : RationalInstance n) (z : Fin (RamFlowData.columns n) → ℚ)
    (y : Fin (RamFlowData.rows n) → ℚ) (hy : ∀ i, 0 ≤ y i)
    (hfit : FitsInWords (sourceWord.eval (bitSize (encodeProgram (program I))))
      (encodeCertificate (.optimal z y))) (ps : List (Fin n)) :
    ∀ u v, LpInputSize.Height
      (2^(widthBound sourceWord).eval (bitSize (encodeInput kind I)))
      (RationalDistances.iterate (RationalDistances.zeroDiagonal (DirectedFlowDual.length y)) ps u v) := by
  let L := bitSize (encodeInput kind I)
  let s := bitSize (encodeProgram (program I))
  let w := sourceWord.eval s
  have hyfit : FitsInWords w (encodeVector y) := by
    intro word hw
    exact hfit word (by simp only [encodeCertificate,List.mem_append]; exact Or.inr hw)
  have hh := vector_height w y hyfit
  have hs : s ≤ LpInputSize.sizeBound.eval L := LpInputSize.flow_program_polynomial_size kind I
  have hn : n ≤ L := LpInputSize.input_dimension kind I
  have hw : w ≤ sourceWord.eval (LpInputSize.sizeBound.eval L) := RamFlowSolverBounds.eval_mono sourceWord hs
  have hexp : w*(n*n+1) ≤ (widthBound sourceWord).eval L := by
    simp only [widthBound,Polynomial.eval_mul,Polynomial.eval_comp,Polynomial.eval_add,
      Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_C]
    have hnn : n*n+1 ≤ L^2+1 := by nlinarith
    exact Nat.mul_le_mul hw hnn
  intro u v
  apply LpInputSize.height_mono (MetricHeight.dual_height y hy w (fun i => (hh i).1) (fun i => (hh i).2) ps u v)
  exact Nat.pow_le_pow_right (by decide) hexp

end Lax455465Proofs.FlowDistanceBounds
