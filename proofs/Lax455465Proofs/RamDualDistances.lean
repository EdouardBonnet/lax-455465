import Lax455465Proofs.RamDualDistancesInit
import Lax455465Proofs.RamFloydBounds

namespace Lax455465Proofs.RamDualDistances

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState MetricMatrix
open scoped NNRat

def command : Com := .seq RamDualDistancesInit.command RamFloydWarshall.command

def result {n : ℕ} (y : Fin (RamFlowData.rows n) → ℚ) (hy : ∀ i, 0 ≤ y i) : Matrix n :=
  iterate (RamDualDistancesInit.matrix y hy) (List.finRange n)

theorem rational_result {n : ℕ} (y : Fin (RamFlowData.rows n) → ℚ) (hy : ∀ i, 0 ≤ y i) :
    rational (result y hy) = RationalDistances.dualDistance y := by
  simpa only [result,RamDualDistancesInit.rational_matrix,RationalDistances.dualDistance,RationalDistances.solve]
    using rational_iterate (RamDualDistancesInit.matrix y hy) (List.finRange n)

/-- Initialize from the actual dual buffer and compute every shortest
rational distance, with no geometry or distance oracle supplied. -/
theorem command_spec (B w : ℕ) {n : ℕ} (y : Fin (RamFlowData.rows n) → ℚ) (hy : ∀ i, 0 ≤ y i)
    (hB : 2*(2*2^(w*(n*n+1)))^2+3 < B)
    (hn : n < B) (hn2 : n*n < B) (hindex : 2*(n*n)+2 < B)
    (hnum : ∀ i, (y i).num.natAbs ≤ 2^w) (hden : ∀ i, (y i).den ≤ 2^w) :
    Spec B (fun σ => σ.vars "lp.n" = n ∧ σ.vars "lp.n2" = n*n ∧
      Prefix (RamUnsignedBuffer.encode (RamOptimalDecode.vector y hy)) "flow.dual" σ ∧
      2*(n*n) < (σ.arrs "metric.old").length ∧ 2*(n*n) < (σ.arrs "metric.new").length) command
      (fun _ τ => τ.vars "metric.n" = n ∧ τ.vars "metric.n2" = n*n ∧
        Prefix (RamUnsignedBuffer.encode (values (result y hy))) "metric.old" τ)
      (50*(n*n)+12+(n*((72*(w*(n*n+1))+324)*(n*n)+22)+10)) := by
  have hpower : 2^w ≤ 2^(w*(n*n+1)) := Nat.pow_le_pow_right (by decide) (by nlinarith)
  have h2 : 2 < B := by nlinarith
  have hM : 2^w < B := by nlinarith [Nat.two_pow_pos (w*(n*n+1))]
  let d := RamDualDistancesInit.matrix y hy
  have hinitNum : ∀ u v, (d u v).num ≤ 2^w := by
    intro u v
    dsimp only [d,RamDualDistancesInit.matrix,RationalDistances.zeroDiagonal]
    split_ifs
    · change NNRat.num (0 : ℚ≥0) ≤ 2^w; simp
    · exact hnum _
  have hinitDen : ∀ u v, (d u v).den ≤ 2^w := by
    intro u v
    dsimp only [d,RamDualDistancesInit.matrix,RationalDistances.zeroDiagonal]
    split_ifs
    · change NNRat.den (0 : ℚ≥0) ≤ 2^w
      simpa using Nat.succ_le_iff.mpr (Nat.two_pow_pos w)
    · exact hden _
  rintro σ ⟨hN,hN2,hdual,hOldRoom,hNewRoom⟩
  obtain ⟨ν,rinit,pinit⟩ := RamDualDistancesInit.command_spec B (2^w) y hy h2 hM hn hn2 hindex hnum hden σ
    ⟨hN,hN2,hdual,hOldRoom⟩
  have hOldRoomν : 2*(n*n) ≤ (ν.arrs "metric.old").length := by
    rw [RamFrames.run_array_length rinit "metric.old"]; omega
  have hNewRoomν : 2*(n*n) < (ν.arrs "metric.new").length := by rwa [RamFrames.run_array_length rinit "metric.new"]
  obtain ⟨τ,rfloyd,pfloyd⟩ := RamFloydBounds.command_spec B w d hB hn hn2 hindex hinitNum hinitDen ν
    ⟨pinit.1.1,pinit.1.2.1,pinit.2,hOldRoomν,hNewRoomν⟩
  exact ⟨τ,rinit.seq rfloyd,pfloyd⟩

end Lax455465Proofs.RamDualDistances
