import Lax455465Proofs.RamVolume
import Lax455465Proofs.VolumeHeight

namespace Lax455465Proofs.RamVolumeDyadic

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning MetricMatrix LpInputSize
open scoped NNRat

/-- Supply every intermediate-height obligation from one coordinate-bit
bound, with a polynomial instruction count for the complete volume query. -/
theorem command_spec (B w : ℕ) {n : ℕ} (outward : Bool) (capacity length : Matrix n)
    (distance : Fin n → ℚ≥0) (seed radius : ℚ≥0)
    (hB : 2*(2^(VolumeHeight.exponent n w))^2+3 < B)
    (hindex : 2*(n*n)+2 < B) (hvertex : 2*n+2 < B)
    (hc : ∀ u v, Height (2^w) (capacity u v : ℚ))
    (hl : ∀ u v, Height (2^w) (length u v : ℚ))
    (hd : ∀ v, Height (2^w) (distance v : ℚ))
    (hs : Height (2^w) (seed : ℚ)) (hr : Height (2^w) (radius : ℚ)) :
    Spec B (RamVolume.Context outward capacity length distance seed radius) (RamVolume.command outward)
      (fun _ τ => RamVolume.Context outward capacity length distance seed radius τ ∧
        RamUnsignedScalar.Stored "region.volume" (VolumeData.value outward capacity length distance seed radius) τ)
      ((216*VolumeHeight.exponent n w+610)*(n*n)+72*VolumeHeight.exponent n w+192) := by
  let H := VolumeHeight.exponent n w
  have hb := VolumeHeight.bounds outward capacity length distance seed radius w hc hl hd hs hr
  have hn {q : ℚ≥0} (hq : Height (2^H) (q : ℚ)) : q.num ≤ 2^H := by simpa only [NNRat.natAbs_num_coe] using hq.1
  have hd' {q : ℚ≥0} (hq : Height (2^H) (q : ℚ)) : q.den ≤ 2^H := by simpa only [NNRat.den_coe] using hq.2
  have spec := RamVolume.command_spec B (2^H) outward capacity length distance seed radius hB hindex hvertex
    (fun u v => hn (hb.capacityBound u v)) (fun u v => hd' (hb.capacityBound u v))
    (fun u v => hn (hb.lengthBound u v)) (fun u v => hd' (hb.lengthBound u v))
    (fun v => hn (hb.distanceBound v)) (fun v => hd' (hb.distanceBound v))
    (hn hb.seedBound) (hd' hb.seedBound) (hn hb.radiusBound) (hd' hb.radiusBound)
    (fun v => hn (hb.differenceBound v)) (fun v => hd' (hb.differenceBound v))
    (fun u v => hn (hb.portionBound u v)) (fun u v => hd' (hb.portionBound u v))
    (fun q hq => hn (hb.coefficientBound q hq)) (fun q hq => hd' (hb.coefficientBound q hq))
    (fun i => hn (hb.prefixBound i)) (fun i => hd' (hb.prefixBound i))
    (hn hb.valueBound) (hd' hb.valueBound)
  intro σ hσ
  obtain ⟨τ,rr,pr⟩ := spec σ hσ
  refine ⟨τ,rr.mono ?_,pr⟩
  rw [←Nat.pow_mul,Nat.size_pow]
  dsimp only [H]
  ring_nf
  omega

end Lax455465Proofs.RamVolumeDyadic
