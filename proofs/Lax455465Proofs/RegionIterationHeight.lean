import Lax455465Proofs.RamRegionSetup
import Lax455465Proofs.ResidualData

namespace Lax455465Proofs.RegionIterationHeight
open LpInputSize Lax455465.RationalEncoding
open scoped NNRat

def exponent (n w : ℕ) : ℕ := RegionQueryHeight.exponent n (2*w)

/-- Every query in every residual iteration has the same polynomial bit
bound. Recomputing residual arrays from the original graph prevents height
bounds from accumulating with the number of removed regions. -/
theorem bounds {n : ℕ} (I : RationalInstance n) (length : MetricMatrix.Matrix n)
    (seed beta delta : ℚ≥0) (k w : ℕ)
    (hw : ∀ v, Height (2^w) (I.weight v : ℚ))
    (hc : ∀ u v, Height (2^w) (I.capacity u v : ℚ))
    (hl : ∀ u v, Height (2^w) (length u v : ℚ))
    (hs : Height (2^w) (seed : ℚ)) (hb : Height (2^w) (beta : ℚ))
    (hd : Height (2^w) (delta : ℚ)) (hu : Height (2^w) ((delta/(k : ℚ≥0) : ℚ≥0) : ℚ))
    (hk : k≤2^w) (active : Finset (Fin n)) (root : Fin n) (r : ℚ≥0)
    (hr : r∈RadiusData.candidates (length root) (fun v => length v root) k delta) :
    RegionQueryHeight.Bounds (RadiusSearchData.atRadius (RamRegionSetup.query
      (ResidualData.weights I active) (ResidualData.capacity I active) length root seed beta) r) (exponent n w) := by
  have hp : 2^w≤2^(2*w) := Nat.pow_le_pow_right (by decide) (by omega)
  have widen {q : ℚ} (h : Height (2^w) q) : Height (2^(2*w)) q := height_mono h hp
  have hrad : Height (2^(2*w)) (r : ℚ) := by
    have h := RadiusData.height (length root) (fun v => length v root) k (2^w) delta
      Nat.one_le_two_pow hk hu hd (hl root) (fun v => hl v root) r hr
    simpa only [←Nat.pow_add,show w+w=2*w by omega] using h
  apply RegionQueryHeight.bounds _ (2*w)
  · exact fun v => widen (ResidualData.weights_height I active w hw v)
  · exact fun u v => widen (ResidualData.capacity_height I active w hc u v)
  · exact fun u v => widen (hl u v)
  · intro b v
    cases b
    · exact widen (hl v root)
    · exact widen (hl root v)
  · exact widen hs
  · exact widen hb
  · exact hrad

end Lax455465Proofs.RegionIterationHeight
