import Lax455465Proofs.RamUnsignedScalar

namespace Lax455465Proofs.RamScalarInverse
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamUnsignedScalar
open scoped NNRat

def command (name : String) : Com := .seq (load name)
  (.seq (RamUnsignedArithmetic.copy "left") invertFraction)

/-- Take the exact reciprocal of a persistent canonical rational. The zero
case returns canonical zero, following the field's inverse convention. -/
theorem command_spec (B : ℕ) (name : String) (q : ℚ≥0) (h1 : 1<B)
    (hn : q.num<B) (hd : q.den<B)
    (hfresh : name++".n"≠"rat.s" ∧ name++".d"≠"rat.s" ∧ name++".d"≠"rat.n") :
    Spec B (Stored name q) (command name)
      (fun _ τ => FractionOutput ((q⁻¹ : ℚ≥0) : ℚ) τ) (36*q.num.size+52) := by
  rintro σ hσ
  obtain ⟨ν,rl,pl⟩ := load_spec B name q h1 hn hd hfresh σ hσ
  obtain ⟨μ,rc,pc⟩ := RamUnsignedArithmetic.copy_spec B q "left" h1 hn hd (by decide) ν pl
  obtain ⟨τ,ri,pi⟩ := invertFraction_spec B 0 q.num q.den h1 (by omega) hn hd μ pc
  exact ⟨τ,(rl.seq (rc.seq ri)).mono (by omega),by simpa only [RamUnsignedArithmetic.value,NNRat.coe_inv] using pi⟩

end Lax455465Proofs.RamScalarInverse
