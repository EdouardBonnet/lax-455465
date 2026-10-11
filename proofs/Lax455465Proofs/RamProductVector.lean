import Lax455465Proofs.RamProductSum
import Lax455465Proofs.RamUnsignedVector
import Lax455465Proofs.LpInputSize

namespace Lax455465Proofs.RamProductVector

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamVirtualState
open scoped NNRat

def Context (leftArray rightArray : String) (xs ys : List ℚ≥0) (σ : Env) : Prop :=
  σ.vars "product.count" = xs.length ∧ Prefix (RamUnsignedBuffer.encode xs) leftArray σ ∧
    Prefix (RamUnsignedBuffer.encode ys) rightArray σ

def command (leftArray rightArray target : String) : Com := .seq (.assign "product.pos" (.lit 0))
  (RamUnsignedVector.command "sum.i" "product.count" target "product.pos" (RamArrayProduct.command leftArray rightArray))

/-- Emit the exact coordinatewise product of two initialized rational
vectors. For zero/one vectors this is the residual membership intersection. -/
theorem command_spec (B M : ℕ) (leftArray rightArray target : String) (xs ys : List ℚ≥0)
    (hlen : ys.length = xs.length) (hneq : leftArray ≠ target ∧ rightArray ≠ target)
    (hB : 2*M^2+3 < B) (hindex : 2*xs.length+2 < B)
    (hxn : ∀ q ∈ xs, q.num ≤ M) (hxd : ∀ q ∈ xs, q.den ≤ M)
    (hyn : ∀ q ∈ ys, q.num ≤ M) (hyd : ∀ q ∈ ys, q.den ≤ M) :
    Spec B (fun σ => Context leftArray rightArray xs ys σ ∧ 2*xs.length < (σ.arrs target).length)
      (command leftArray rightArray target) (fun _ τ => Context leftArray rightArray xs ys τ ∧
        Prefix (RamUnsignedBuffer.encode (RamProductSum.products xs ys)) target τ)
      ((36*(M^2).size+126)*xs.length+8) := by
  have hM : M < B := by nlinarith
  have hprod : M*M < B := by nlinarith
  let qs := RamProductSum.products xs ys
  have hqlen : qs.length = xs.length := List.length_ofFn
  have hvalues : ∀ i, ∀ hi : i < qs.length, qs[i].num < B ∧ qs[i].den < B := by
    intro i hi
    have hx : i < xs.length := by rwa [hqlen] at hi
    have hy : i < ys.length := by omega
    have hxm : xs[i] ∈ xs := List.getElem_mem hx
    have hym : ys[i] ∈ ys := List.getElem_mem hy
    have hh := LpInputSize.height_mul
      (show LpInputSize.Height M (xs[i] : ℚ) from ⟨by simpa only [NNRat.natAbs_num_coe] using hxn _ hxm,
        by simpa only [NNRat.den_coe] using hxd _ hxm⟩)
      (show LpInputSize.Height M (ys[i] : ℚ) from ⟨by simpa only [NNRat.natAbs_num_coe] using hyn _ hym,
        by simpa only [NNRat.den_coe] using hyd _ hym⟩)
    have he : qs[i] = xs[i]*ys[i] := RamProductSum.value_at xs ys hlen i hx
    rw [he]
    have hh' : LpInputSize.Height (M*M) ((xs[i]*ys[i] : ℚ≥0) : ℚ) := by
      simpa only [NNRat.coe_mul] using hh
    have hn : (xs[i]*ys[i]).num ≤ M*M := by simpa only [NNRat.natAbs_num_coe] using hh'.1
    have hd : (xs[i]*ys[i]).den ≤ M*M := by simpa only [NNRat.den_coe] using hh'.2
    exact ⟨hn.trans_lt hprod,hd.trans_lt hprod⟩
  have hbody : ∀ i, ∀ hi : i < qs.length,
      Spec B (fun σ => Context leftArray rightArray xs ys σ ∧ σ.vars "sum.i" = i)
        (RamArrayProduct.command leftArray rightArray)
        (fun _ τ => Context leftArray rightArray xs ys τ ∧ FractionOutput (qs[i] : ℚ) τ)
        (36*(M^2).size+104) := by
    intro i hi σ hσ
    have hx : i < xs.length := by rwa [hqlen] at hi
    have hy : i < ys.length := by omega
    have hxm : xs[i] ∈ xs := List.getElem_mem hx
    have hym : ys[i] ∈ ys := List.getElem_mem hy
    obtain ⟨τ,rr,pr⟩ := RamArrayProduct.command_spec B M leftArray rightArray xs ys i hx hy hB
      (by omega) (hxn _ hxm) (hxd _ hxm) (hyn _ hym) (hyd _ hym) σ ⟨hσ.1.2.1,hσ.1.2.2,hσ.2⟩
    have hcost : (xs[i].den*ys[i].den).size ≤ (M^2).size :=
      Nat.size_le_size (by nlinarith [Nat.mul_le_mul (hxd _ hxm) (hyd _ hym)])
    refine ⟨τ,rr.mono (by omega),?_,?_⟩
    · simpa only [Context,Prefix,rr.frame_var "product.count" (by
        dsimp [RamArrayProduct.command,RamUnsignedBuffer.read,RamUnsignedArithmetic.copy,Com.wvars]; decide),
        rr.frame_arr leftArray (by change leftArray ∉ ([] : List String); simp),
        rr.frame_arr rightArray (by change rightArray ∉ ([] : List String); simp)] using hσ.1
    · simpa only [qs,RamProductSum.value_at xs ys hlen i hx] using pr
  have hf := RamUnsignedVector.command_spec B (36*(M^2).size+104)
    (Context leftArray rightArray xs ys) "sum.i" "product.count" target "product.pos" qs []
    (RamArrayProduct.command leftArray rightArray) (by nlinarith)
    (by simp only [List.length_nil,hqlen]; omega)
    (fun i hi => (hvalues i hi).1) (fun i hi => (hvalues i hi).2)
    (fun _ h => by simpa only [hqlen] using h.1)
    (fun σ k h => by simpa only [Context,Prefix,vars_setVar,arrs_setVar,String.reduceEq,if_false] using h)
    hbody
    (by dsimp [RamArrayProduct.command,RamUnsignedBuffer.read,RamUnsignedArithmetic.copy,Com.wvars]; decide)
    (by dsimp [RamArrayProduct.command,RamUnsignedBuffer.read,RamUnsignedArithmetic.copy,Com.wvars]; decide)
    (by change target ∉ ([] : List String); simp)
    (by dsimp [RamUnsignedEncoding.command,RamWordBuffer.append,Com.wvars]; decide)
    (fun rr h => by
      simpa only [Context,Prefix,
        rr.frame_var "product.count" (by dsimp [RamUnsignedEncoding.command,RamWordBuffer.append,Com.wvars]; decide),
        rr.frame_arr leftArray (by simp [RamUnsignedEncoding.command,RamWordBuffer.append,Com.warrs,hneq.1]),
        rr.frame_arr rightArray (by simp [RamUnsignedEncoding.command,RamWordBuffer.append,Com.warrs,hneq.2])] using h)
    (by decide) (by decide)
  rintro σ ⟨hctx,hroom⟩
  let ν := σ.setVar "product.pos" 0
  have rzero : Run B (.assign "product.pos" (.lit 0)) σ ν 2 := Run.assign (evalB_lit (by nlinarith))
  have hctxν : Context leftArray rightArray xs ys ν := by
    simpa only [Context,Prefix,ν,vars_setVar,arrs_setVar,String.reduceEq,if_false] using hctx
  obtain ⟨τ,rr,pr⟩ := hf ν ⟨hctxν,by intro i hi; simp at hi,by simp [ν],
    by simpa only [ν,arrs_setVar,List.length_nil,Nat.zero_add,hqlen] using hroom⟩
  refine ⟨τ,(rzero.seq rr).mono ?_,pr.1,by simpa only [List.nil_append,qs] using pr.2.1⟩
  simp only [hqlen,Nat.add_assoc,Nat.reduceAdd]
  omega

end Lax455465Proofs.RamProductVector
