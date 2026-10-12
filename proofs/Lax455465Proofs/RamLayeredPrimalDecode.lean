import Lax455465Proofs.RamOptimalDecode
import Lax455465Proofs.RamLayeredData

namespace Lax455465Proofs.RamLayeredPrimalDecode
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamLayeredData LayeredLpFlat
open Lax109476.RationalEncoding Lax109476.RationalCertificates RamOptimalDecode
open scoped NNRat

def command : Com := .seq (.assign "cert.cursor" (.lit 1))
  (.seq (.assign "cert.count" (.var "lp.columns")) (RamCertificateVector.command "flow.primal"))

/-- Decode precisely the primal coordinates emitted by the registered LP
solver. The layer and all graph dimensions remain runtime data. -/
theorem command_spec (B : ℕ) {n L : ℕ} (I : Lax455465.RationalEncoding.RationalInstance n)
    (z : Fin (columns n L) → ℚ) (y : Fin (rows n L) → ℚ) (hz : ∀ i,0≤z i)
    (h3 : 3<B) (hlen : 1+3*columns n L+3<B)
    (hnum : ∀ q∈vector z hz,q.num<B) (hden : ∀ q∈vector z hz,q.den<B) :
    Spec B (fun σ => Data I L σ ∧ Prefix (encodeCertificate (.optimal z y)) "vm.output" σ ∧
      2*columns n L<(σ.arrs "flow.primal").length) command
      (fun _ τ => Data I L τ ∧ Prefix (RamUnsignedBuffer.encode (vector z hz)) "flow.primal" τ)
      (39*columns n L+12) := by
  rintro σ ⟨hd,hp,hroom⟩
  let ν := (σ.setVar "cert.cursor" 1).setVar "cert.count" (columns n L)
  have r1 : Run B (.assign "cert.cursor" (.lit 1)) σ (σ.setVar "cert.cursor" 1) 2 := Run.assign (evalB_lit (by omega))
  have r2 : Run B (.assign "cert.count" (.var "lp.columns")) (σ.setVar "cert.cursor" 1) ν 2 :=
    Run.assign (by rw [evalB_var_iff]; exact ⟨by simpa only [vars_setVar,String.reduceEq,if_false] using hd.columnCount.symm,
      by simpa only [vars_setVar,String.reduceEq,if_false] using hd.columnCount ▸ (by omega : columns n L<B)⟩)
  have he : encodeCertificate (.optimal z y)=[0]++(RamCertificateVector.source (vector z hz)++encodeVector y) := by
    simp only [encodeCertificate,source_vector,List.append_assoc]
  obtain ⟨τ,rr,pr⟩ := RamCertificateVector.command_spec B [0] (encodeVector y) (vector z hz) "flow.primal"
    h3 (by simp only [List.length_cons,List.length_nil,length_vector]; omega) hnum hden (by decide) ν
    ⟨by simpa only [←he,Prefix,ν,arrs_setVar] using hp,by simp [ν],by simp [ν],
      by simpa only [length_vector,ν,arrs_setVar] using hroom⟩
  have whole := r1.seq (r2.seq rr)
  exact ⟨τ,whole.mono (by simp only [length_vector]; omega),
    RamLayeredData.frame whole I L hd (by decide) (by decide),pr.2.2.1⟩

end Lax455465Proofs.RamLayeredPrimalDecode
