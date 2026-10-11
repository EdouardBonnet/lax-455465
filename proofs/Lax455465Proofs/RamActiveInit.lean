import Lax455465Proofs.RamUnsignedVector
import Lax455465Proofs.RamFractionPrimitives
import Lax455465Proofs.MaskedMassData

namespace Lax455465Proofs.RamActiveInit

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamRational
open scoped NNRat

def command : Com := .seq (.assign "active.position" (.lit 0))
  (RamUnsignedVector.command "active.i" "metric.n" "region.active" "active.position" RamFractionPrimitives.one)

/-- Initially every vertex is active, including zero-weight vertices that
may be needed as transit points by the multicommodity flow. -/
theorem command_spec (B n : ℕ) (h2 : 2 < B) (hindex : 2*n+2 < B) :
    Spec B (fun σ => σ.vars "metric.n" = n ∧ 2*n < (σ.arrs "region.active").length)
      command (fun _ τ => τ.vars "metric.n" = n ∧
        Prefix (RamUnsignedBuffer.encode (MaskedMassData.flags (fun _ : Fin n => true))) "region.active" τ)
      (28*n+8) := by
  let qs := MaskedMassData.flags (fun _ : Fin n => true)
  have hlen : qs.length = n := List.length_ofFn
  have hv : ∀ i, ∀ hi : i < qs.length, qs[i] = 1 := by
    intro i hi
    simp [qs,MaskedMassData.flags]
  have hloop := RamUnsignedVector.command_spec B 6 (fun σ => σ.vars "metric.n" = n)
    "active.i" "metric.n" "region.active" "active.position" qs [] RamFractionPrimitives.one (by omega)
    (by simp only [List.length_nil,hlen]; omega)
    (fun i hi => by rw [hv i hi]; simp; omega) (fun i hi => by rw [hv i hi]; simp; omega)
    (fun _ h => by simpa only [hlen] using h)
    (fun σ k h => by simpa only [vars_setVar,String.reduceEq,if_false] using h)
    (fun i hi σ h => by
      obtain ⟨τ,rr,pr⟩ := RamFractionPrimitives.one_spec B (by omega) σ True.intro
      exact ⟨τ,rr,by simpa only [rr.frame_var "metric.n" (by decide)] using h.1,by simpa only [hv i hi,NNRat.coe_one] using pr⟩)
    (by decide) (by decide) (by decide) (by decide)
    (fun rr h => by simpa only [rr.frame_var "metric.n" (by decide)] using h)
    (by decide) (by decide)
  rintro σ ⟨hn,hroom⟩
  let ν := σ.setVar "active.position" 0
  have rzero : Run B (.assign "active.position" (.lit 0)) σ ν 2 := Run.assign (evalB_lit (by omega))
  obtain ⟨τ,rr,pr⟩ := hloop ν ⟨by simpa only [ν,vars_setVar,String.reduceEq,if_false] using hn,
    by intro i hi; simp at hi,by simp [ν],by simpa only [ν,arrs_setVar,hlen,List.length_nil,Nat.zero_add] using hroom⟩
  exact ⟨τ,(rzero.seq rr).mono (by simp only [hlen]; omega),pr.1,by simpa only [qs,List.nil_append] using pr.2.1⟩

end Lax455465Proofs.RamActiveInit
