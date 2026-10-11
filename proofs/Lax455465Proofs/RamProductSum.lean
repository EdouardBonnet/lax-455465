import Lax455465Proofs.RamArrayProduct
import Lax455465Proofs.RamUnsignedSum
import Mathlib.Data.List.GetD

namespace Lax455465Proofs.RamProductSum

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamVirtualState
open scoped NNRat

def products (xs ys : List ℚ≥0) : List ℚ≥0 :=
  List.ofFn fun i : Fin xs.length => xs[i.val] * ys.getD i.val 0

def Context (leftArray rightArray : String) (xs ys : List ℚ≥0) (σ : Env) : Prop :=
  σ.vars "sum.count" = xs.length ∧ Prefix (RamUnsignedBuffer.encode xs) leftArray σ ∧
    Prefix (RamUnsignedBuffer.encode ys) rightArray σ

def command (leftArray rightArray : String) : Com :=
  RamUnsignedSum.command "sum.i" "sum.count" (RamArrayProduct.command leftArray rightArray)

theorem value_at (xs ys : List ℚ≥0) (hlen : ys.length = xs.length) (i : ℕ) (hi : i < xs.length) :
    (products xs ys)[i]'(by simpa only [products,List.length_ofFn] using hi) =
      xs[i]*ys[i]'(by omega) := by
  simp only [products,List.getElem_ofFn,List.getD_eq_get ys 0 (⟨i,by omega⟩ : Fin ys.length)]
  rfl

/-- Native dot product of two rational vectors. In particular this computes
the metric cost from the source capacity and computed distance buffers. -/
theorem command_spec (B M : ℕ) (leftArray rightArray : String) (xs ys : List ℚ≥0)
    (hlen : ys.length = xs.length) (hB : 2*M^2+3 < B) (hindex : 2*xs.length+2 < B)
    (hxn : ∀ q ∈ xs, q.num ≤ M) (hxd : ∀ q ∈ xs, q.den ≤ M)
    (hyn : ∀ q ∈ ys, q.num ≤ M) (hyd : ∀ q ∈ ys, q.den ≤ M)
    (hpn : ∀ q ∈ products xs ys, q.num ≤ M) (hpd : ∀ q ∈ products xs ys, q.den ≤ M)
    (hprefixNum : ∀ i, ((products xs ys).take i).sum.num ≤ M)
    (hprefixDen : ∀ i, ((products xs ys).take i).sum.den ≤ M) :
    Spec B (Context leftArray rightArray xs ys) (command leftArray rightArray)
      (fun _ τ => Context leftArray rightArray xs ys τ ∧ FractionOutput (((products xs ys).sum : ℚ≥0) : ℚ) τ)
      ((72*(M^2).size+224)*xs.length+16) := by
  have hlength : (products xs ys).length = xs.length := List.length_ofFn
  have hbody : ∀ i, ∀ hi : i < (products xs ys).length,
      Spec B (fun σ => Context leftArray rightArray xs ys σ ∧ σ.vars "sum.i" = i)
        (RamArrayProduct.command leftArray rightArray)
        (fun _ τ => Context leftArray rightArray xs ys τ ∧ FractionOutput ((products xs ys)[i] : ℚ) τ)
        (36*(M^2).size+104) := by
    intro i hi σ hσ
    have hx : i < xs.length := by rwa [hlength] at hi
    have hy : i < ys.length := by omega
    have hxm : xs[i] ∈ xs := List.getElem_mem hx
    have hym : ys[i] ∈ ys := List.getElem_mem hy
    obtain ⟨τ,rr,pr⟩ := RamArrayProduct.command_spec B M leftArray rightArray xs ys i hx hy hB
      (by omega) (hxn _ hxm) (hxd _ hxm) (hyn _ hym) (hyd _ hym) σ ⟨hσ.1.2.1,hσ.1.2.2,hσ.2⟩
    have hcost : (xs[i].den*ys[i].den).size ≤ (M^2).size :=
      Nat.size_le_size (by nlinarith [Nat.mul_le_mul (hxd _ hxm) (hyd _ hym)])
    refine ⟨τ,rr.mono (by omega),?_,?_⟩
    · simpa only [Context,Prefix,rr.frame_var "sum.count" (by
        dsimp [RamArrayProduct.command,RamUnsignedBuffer.read,RamUnsignedArithmetic.copy,Com.wvars]; decide),
        rr.frame_arr leftArray (by change leftArray ∉ ([] : List String); simp),
        rr.frame_arr rightArray (by change rightArray ∉ ([] : List String); simp)] using hσ.1
    · simpa only [value_at xs ys hlen i hx] using pr
  have hf := RamUnsignedSum.command_spec B M (36*(M^2).size+104)
    (Context leftArray rightArray xs ys) "sum.i" "sum.count" (products xs ys)
    (RamArrayProduct.command leftArray rightArray) hB (by rw [hlength]; omega) hpn hpd hprefixNum hprefixDen
    (fun σ h => by simpa only [hlength] using h.1)
    (fun σ k name h hn => by
      rcases hn with rfl | rfl | rfl <;>
        simpa only [Context,Prefix,vars_setVar,arrs_setVar,String.reduceEq,if_false] using h)
    hbody (by decide)
    (by dsimp [RamArrayProduct.command,RamUnsignedBuffer.read,RamUnsignedArithmetic.copy,Com.wvars]; decide)
    (by dsimp [RamArrayProduct.command,RamUnsignedBuffer.read,RamUnsignedArithmetic.copy,Com.wvars]; decide)
    (fun rr h => by
      simpa only [Context,Prefix,rr.frame_var "sum.count" (by decide),
        rr.frame_arr leftArray (by change leftArray ∉ ([] : List String); simp),
        rr.frame_arr rightArray (by change rightArray ∉ ([] : List String); simp)] using h)
    (fun rr h => by
      simpa only [Context,Prefix,rr.frame_var "sum.count" (by decide),
        rr.frame_arr leftArray (by change leftArray ∉ ([] : List String); simp),
        rr.frame_arr rightArray (by change rightArray ∉ ([] : List String); simp)] using h)
  unfold command
  rw [hlength] at hf
  convert hf using 1 <;> ring

end Lax455465Proofs.RamProductSum
