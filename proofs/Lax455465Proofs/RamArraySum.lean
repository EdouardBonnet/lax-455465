import Lax455465Proofs.RamUnsignedSum
import Lax455465Proofs.RamUnsignedBuffer

namespace Lax455465Proofs.RamArraySum

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamVirtualState
open scoped NNRat

def Context (array : String) (qs : List ℚ≥0) (σ : Env) : Prop :=
  σ.vars "sum.count" = qs.length ∧ Prefix (RamUnsignedBuffer.encode qs) array σ

def command (array : String) : Com :=
  RamUnsignedSum.command "sum.i" "sum.count" (RamUnsignedBuffer.read array "sum.i")

/-- Sum an initialized unsigned rational buffer using the exact normalized
native accumulator. The empty vector produces canonical zero. -/
theorem command_spec (B M : ℕ) (array : String) (qs : List ℚ≥0) (hB : 2*M^2+3 < B)
    (hindex : 2*qs.length+2 < B)
    (hnum : ∀ q ∈ qs, q.num ≤ M) (hden : ∀ q ∈ qs, q.den ≤ M)
    (hprefixNum : ∀ i, (qs.take i).sum.num ≤ M) (hprefixDen : ∀ i, (qs.take i).sum.den ≤ M) :
    Spec B (Context array qs) (command array)
      (fun _ τ => Context array qs τ ∧ FractionOutput ((qs.sum : ℚ≥0) : ℚ) τ)
      ((36*(M^2).size+134)*qs.length+16) := by
  have hM : M < B := by nlinarith
  have hread : ∀ i, ∀ hi : i < qs.length,
      Spec B (fun σ => Context array qs σ ∧ σ.vars "sum.i" = i)
        (RamUnsignedBuffer.read array "sum.i")
        (fun _ τ => Context array qs τ ∧ FractionOutput (qs[i] : ℚ) τ) 14 := by
    intro i hi σ hσ
    have hq : qs[i] ∈ qs := List.getElem_mem hi
    obtain ⟨τ,rr,pr⟩ := RamUnsignedBuffer.read_spec B array "sum.i" qs i hi (by nlinarith)
      (by omega) ((hnum _ hq).trans_lt hM) ((hden _ hq).trans_lt hM) (by decide) σ ⟨hσ.1.2,hσ.2⟩
    refine ⟨τ,rr,?_,pr.1⟩
    simpa only [Context,Prefix,rr.frame_var "sum.count" (by simp [RamUnsignedBuffer.read,Com.wvars]),
      rr.frame_arr array (by simp [RamUnsignedBuffer.read,Com.warrs])] using hσ.1
  have hf := RamUnsignedSum.command_spec B M 14 (Context array qs) "sum.i" "sum.count" qs
    (RamUnsignedBuffer.read array "sum.i") hB (by omega) hnum hden hprefixNum hprefixDen
    (fun _ h => h.1)
    (fun σ k name h hn => by
      rcases hn with rfl | rfl | rfl <;>
        simpa only [Context,Prefix,vars_setVar,arrs_setVar,String.reduceEq,if_false] using h)
    hread (by decide) (by simp [RamUnsignedBuffer.read,Com.wvars])
    (by simp [RamUnsignedBuffer.read,Com.wvars])
    (fun rr h => by
      simpa only [Context,Prefix,rr.frame_var "sum.count" (by decide),rr.frame_arr array (by change array ∉ ([] : List String); simp)] using h)
    (fun rr h => by
      simpa only [Context,Prefix,rr.frame_var "sum.count" (by decide),rr.frame_arr array (by change array ∉ ([] : List String); simp)] using h)
  unfold command
  convert hf using 1 <;> ring

end Lax455465Proofs.RamArraySum
