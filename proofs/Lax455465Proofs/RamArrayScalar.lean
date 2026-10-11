import Lax455465Proofs.RamUnsignedBuffer
import Lax455465Proofs.RamUnsignedScalar

namespace Lax455465Proofs.RamArrayScalar

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar
open scoped NNRat

def command (array index name : String) : Com := .seq (RamUnsignedBuffer.read array index) (save name)

/-- Copy an initialized canonical vector coordinate into persistent scalar
registers, for the repeated region-volume calculations. -/
theorem command_spec (B : ℕ) (array index name : String) (qs : List ℚ≥0) (i : ℕ)
    (hi : i < qs.length) (h2 : 2 < B) (hindex : 2*i+1 < B)
    (hn : qs[i].num < B) (hd : qs[i].den < B)
    (hfresh : index ≠ "rat.n" ∧ index ≠ "rat.d" ∧ index ≠ "rat.s")
    (hname : name ++ ".n" ≠ "rat.d") :
    Spec B (fun σ => Prefix (RamUnsignedBuffer.encode qs) array σ ∧ σ.vars index=i)
      (command array index name) (fun _ τ => Stored name qs[i] τ) 18 := by
  intro σ hσ
  obtain ⟨ν,rr,pr⟩ := RamUnsignedBuffer.read_spec B array index qs i hi h2 hindex hn hd hfresh σ hσ
  obtain ⟨τ,rs,ps⟩ := save_spec B name qs[i] hn hd hname ν pr.1
  exact ⟨τ,rr.seq rs,ps⟩

end Lax455465Proofs.RamArrayScalar
