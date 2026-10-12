import Lax455465Proofs.LayeredOptimalCertificate
import Lax455465Proofs.RamLpRationalRead

namespace Lax455465Proofs.RamLayeredValue
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamVirtualState
open LayeredFlowLP LayeredFlowDual Lax109476.RationalEncoding

def command : Com := .seq (.assign "cert.cursor" (.lit 1)) RamLpRationalRead.command

/-- Read the actual primal value from the registered solver's optimal output. -/
theorem command_spec (B : ℕ) {n L : ℕ} (f : ℚ) (x : Arc n L → ℚ) (y : Dual n L)
    (hB : 4 < B)
    (hwords : ∀ k ∈ encodeCertificate (.optimal (vector f x) y),k < B) :
    Spec B (Prefix (encodeCertificate (.optimal (vector f x) y)) "vm.output") command
      (fun _ τ => FractionOutput f τ) 19 := by
  obtain ⟨tail,he⟩ := LayeredOptimalCertificate.encoding_head f x y
  have hnum : f.num.natAbs < B := hwords _ (by rw [he]; simp [encodeRational])
  have hden : f.den < B := hwords _ (by rw [he]; simp [encodeRational])
  intro σ hp
  let ν := σ.setVar "cert.cursor" 1
  have ri : Run B (.assign "cert.cursor" (.lit 1)) σ ν 2 := Run.assign (evalB_lit (by omega))
  obtain ⟨τ,rr,pr⟩ := RamLpRationalRead.command_spec B f [0] tail (by omega)
    (by simpa using hB) hnum hden ν ⟨by simpa only [←he,Prefix,ν,arrs_setVar] using hp,by simp [ν]⟩
  exact ⟨τ,ri.seq rr,pr.1⟩

end Lax455465Proofs.RamLayeredValue
