import Lax455465Proofs.RamFloydWarshall
import Lax455465Proofs.MetricPrefixBounds

namespace Lax455465Proofs.RamFloydBounds

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState MetricMatrix
open scoped NNRat

/-- Runtime distance computation requires bounds only on its initial
canonical coordinates. Common-denominator proofs discharge every later
addition, comparison, normalization, and matrix-copy bound. -/
theorem command_spec (B w : ℕ) {n : ℕ} (d : Matrix n)
    (hB : 2*(2*2^(w*(n*n+1)))^2+3 < B)
    (hn : n < B) (hn2 : n*n < B) (hindex : 2*(n*n)+2 < B)
    (hnum : ∀ u v, (d u v).num ≤ 2^w) (hden : ∀ u v, (d u v).den ≤ 2^w) :
    Spec B (fun σ => σ.vars "metric.n" = n ∧ σ.vars "metric.n2" = n*n ∧
      Prefix (RamUnsignedBuffer.encode (values d)) "metric.old" σ ∧
      2*(n*n) ≤ (σ.arrs "metric.old").length ∧ 2*(n*n) < (σ.arrs "metric.new").length)
      RamFloydWarshall.command
      (fun _ τ => τ.vars "metric.n" = n ∧ τ.vars "metric.n2" = n*n ∧
        Prefix (RamUnsignedBuffer.encode (values (iterate d (List.finRange n)))) "metric.old" τ)
      (n*((72*(w*(n*n+1))+324)*(n*n)+22)+10) := by
  let H := 2^(w*(n*n+1))
  have hpheight := MetricPrefixBounds.coordinate_height d w
  have hcand := MetricPrefixBounds.candidate_height d w
  have hnum' : ∀ k ≤ n, ∀ u v, (afterPivots d k u v).num ≤ H := by
    intro k hk u v
    simpa only [LpInputSize.Height,NNRat.natAbs_num_coe] using (hpheight k hnum hden u v).1
  have hden' : ∀ k ≤ n, ∀ u v, (afterPivots d k u v).den ≤ H := by
    intro k hk u v
    simpa only [LpInputSize.Height,NNRat.den_coe] using (hpheight k hnum hden u v).2
  have hsn : ∀ k, ∀ hk : k < n, ∀ u v,
      (afterPivots d k u ⟨k,hk⟩+afterPivots d k ⟨k,hk⟩ v).num ≤ 2*H := by
    intro k hk u v
    simpa only [NNRat.natAbs_num_coe] using (hcand k hnum hden u ⟨k,hk⟩ v).1
  have hsd : ∀ k, ∀ hk : k < n, ∀ u v,
      (afterPivots d k u ⟨k,hk⟩+afterPivots d k ⟨k,hk⟩ v).den ≤ 2*H := by
    intro k hk u v
    simpa only [NNRat.den_coe] using (hcand k hnum hden u ⟨k,hk⟩ v).2
  have hrun := RamFloydWarshall.command_spec B H d hB hn hn2 hindex hnum' hden' hsn hsd
  have hsize : (H*H).size = 2*(w*(n*n+1))+1 := by
    dsimp only [H]
    rw [←Nat.pow_add,Nat.size_pow]
    omega
  convert hrun using 1
  rw [hsize]
  ring

end Lax455465Proofs.RamFloydBounds
