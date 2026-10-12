import Lax455465Proofs.RamUnsignedScalar

namespace Lax455465Proofs.RamNatScalar
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamUnsignedScalar
open scoped NNRat

def command (source target : String) : Com := .seq (.assign (target++".n") (.var source))
  (.assign (target++".d") (.lit 1))

/-- Store a runtime natural number as its canonical unsigned rational pair. -/
theorem command_spec (B v : ℕ) (source target : String) (hv : v<B) (h1 : 1<B) :
    Spec B (fun σ => σ.vars source=v) (command source target)
      (fun _ τ => Stored target (v : ℚ≥0) τ) 4 := by
  run_vcg
  all_goals simp_all [Stored,NNRat.num_natCast,NNRat.den_natCast]

end Lax455465Proofs.RamNatScalar
