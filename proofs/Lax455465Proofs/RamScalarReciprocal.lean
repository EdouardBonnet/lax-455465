import Lax455465Proofs.RamScalarInverse
import Lax455465Proofs.RoundingConstants
import Lax455465Proofs.RamRegionContext

namespace Lax455465Proofs.RamScalarReciprocal
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamUnsignedScalar RamRegionContext
open scoped NNRat

def command (source target : String) : Com := .seq (RamScalarInverse.command source) (save target)

/-- Save the exact reciprocal while retaining a coordinate-height bound.
This computes the inverses used by region-growth constants. -/
theorem command_spec (B M : ℕ) (q : ℚ≥0) (source target : String) (hM : 1≤M) (hB : M<B)
    (hq : LpInputSize.Height M (q : ℚ))
    (hsource : source++".n"≠"rat.s" ∧ source++".d"≠"rat.s" ∧ source++".d"≠"rat.n")
    (htarget : target++".n"≠"rat.d") :
    Spec B (Stored source q) (command source target) (fun _ τ => Stored target q⁻¹ τ)
      (36*q.num.size+56) := by
  have hi := RoundingConstants.inverse_height hM hq
  rintro σ hσ
  obtain ⟨ν,rr,pr⟩ := RamScalarInverse.command_spec B source q (by omega)
    ((num_bound hq).trans_lt hB) ((den_bound hq).trans_lt hB) hsource σ hσ
  obtain ⟨τ,rs,ps⟩ := save_spec B target q⁻¹ ((num_bound hi).trans_lt hB) ((den_bound hi).trans_lt hB) htarget ν pr
  exact ⟨τ,(rr.seq rs).mono (by omega),ps⟩

end Lax455465Proofs.RamScalarReciprocal
