import Lax455465Proofs.RamDecodeFraction
import Lax455465Proofs.RamUnsignedEncoding
import Lax455465Proofs.RamInputSlice

namespace Lax455465Proofs.RamDecodeVector

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamVirtualState
open scoped NNRat

def step (array cursor : String) : Com := .seq RamDecodeFraction.pair
  (.seq (RamUnsignedEncoding.command array cursor)
    (.assign "decode.i" (.add (.var "decode.i") (.lit 1))))

def command (array cursor : String) : Com := .seq (.assign cursor (.lit 0))
  (.seq (.assign "decode.i" (.lit 0))
    (.while (.lt (.var "decode.i") (.var "decode.count")) (step array cursor)))

def Invariant (front tail : List ℕ) (qs : List ℚ≥0) (array cursor : String) (σ : Env) : Prop :=
  Prefix (front ++ (RamUnsignedBuffer.encode qs ++ tail)) "input.data" σ ∧
    σ.vars "decode.count" = qs.length ∧ σ.vars "decode.i" ≤ qs.length ∧
    σ.vars "decode.cursor" = front.length+2*σ.vars "decode.i" ∧
    Prefix (RamUnsignedBuffer.encode (qs.take (σ.vars "decode.i"))) array σ ∧
    σ.vars cursor = 2*σ.vars "decode.i" ∧ 2*qs.length < (σ.arrs array).length

theorem step_spec (B K : ℕ) (front tail : List ℕ) (qs : List ℚ≥0) (array cursor : String)
    (h2 : 2 < B) (hlen : (front ++ (RamUnsignedBuffer.encode qs ++ tail)).length+2 < B)
    (hwords : ∀ x ∈ front ++ (RamUnsignedBuffer.encode qs ++ tail), x < B)
    (hsize : ∀ q ∈ qs, q.den.size ≤ K) (harray : array ≠ "input.data")
    (hfresh : cursor ∉ RamDecodeFraction.pair.wvars)
    (hf : cursor ≠ "decode.count" ∧ cursor ≠ "decode.i" ∧ cursor ≠ "decode.cursor" ∧ cursor ≠ "rat.d") :
    Spec B (fun σ => Invariant front tail qs array cursor σ ∧ σ.vars "decode.i" < qs.length)
      (step array cursor) (fun σ τ => Invariant front tail qs array cursor τ ∧
        τ.vars "decode.i" = σ.vars "decode.i"+1) (36*K+52) := by
  rintro σ ⟨⟨hp,hcount,hi,hcursor,htarget,hpos,hroom⟩,hlt⟩
  let i := σ.vars "decode.i"
  let words := front ++ (RamUnsignedBuffer.encode qs ++ tail)
  have hi' : i < qs.length := hlt
  have hi0 : i ≤ qs.length := hi
  have hindex : front.length+2*i+1 < words.length := RamInputSlice.index_bound front tail qs i hi'
  have hindex0 : front.length+2*i < words.length := by omega
  have hnum : words[front.length+2*i] = qs[i].num := by
    have ho : words[front.length+2*i]? = some qs[i].num := RamInputSlice.numerator front tail qs i hi'
    rw [List.getElem?_eq_getElem hindex0] at ho
    exact Option.some.inj ho
  have hden : words[front.length+2*i+1] = qs[i].den := by
    have ho : words[front.length+2*i+1]? = some qs[i].den := RamInputSlice.denominator front tail qs i hi'
    rw [List.getElem?_eq_getElem hindex] at ho
    exact Option.some.inj ho
  have hnB : qs[i].num < B := by rw [←hnum]; exact hwords _ (List.getElem_mem hindex0)
  have hdB : qs[i].den < B := by rw [←hden]; exact hwords _ (List.getElem_mem hindex)
  have hdSize : qs[i].den.size ≤ K := hsize _ (List.getElem_mem hi')
  have hlength : (RamUnsignedBuffer.encode (qs.take i)).length = 2*i := by
    simp only [RamUnsignedBuffer.length_encode,List.length_take,Nat.min_eq_left hi0]
  obtain ⟨ν,hpair,hpairPost⟩ := RamDecodeFraction.pair_spec B words (front.length+2*i) h2 hindex
    (by dsimp only [words] at hindex; omega) hwords σ ⟨hp,hcursor⟩
  have hfraction : FractionOutput (qs[i] : ℚ) ν := by
    simpa only [hnum,hden,NNRat.num_divNat_den] using hpairPost.2.2
  have htν : Prefix (RamUnsignedBuffer.encode (qs.take i)) array ν := by
    simpa only [Prefix,hpair.frame_arr array (by simp [RamDecodeFraction.pair,RamDecodeFraction.normalize,
      RamArithmetic.normalizeFraction,RamArithmetic.gcdLoop,RamArithmetic.gcdDoubleStep,RamArithmetic.gcdStep,Com.warrs])]
      using htarget
  have hposν : ν.vars cursor = 2*i := (hpair.frame_var cursor hfresh).trans hpos
  have hiν : ν.vars "decode.i" = i := (hpair.frame_var "decode.i" (by decide)).trans rfl
  have hcν : ν.vars "decode.count" = qs.length := (hpair.frame_var "decode.count" (by decide)).trans hcount
  have hroomν : 2*qs.length < (ν.arrs array).length := by rwa [RamFrames.run_array_length hpair array]
  obtain ⟨μ,hemit,hemitPost⟩ := RamUnsignedEncoding.command_spec B array cursor qs[i]
    (RamUnsignedBuffer.encode (qs.take i)) (by omega) hnB hdB
    (by rw [hlength]; simp only [List.length_append,RamUnsignedBuffer.length_encode] at hlen; omega) hf.2.2.2 ν
      ⟨hfraction,htν,by rwa [hlength],by rw [hlength]; omega⟩
  have hpμ : Prefix words "input.data" μ := by
    simpa only [Prefix,hemit.frame_arr "input.data" (by simp [RamUnsignedEncoding.command,RamWordBuffer.append,
      Com.warrs,Ne.symm harray])] using hpairPost.1
  have hcurμ : μ.vars "decode.cursor" = front.length+2*i+2 :=
    (hemit.frame_var "decode.cursor" (by simp [RamUnsignedEncoding.command,RamWordBuffer.append,Com.wvars,
      Ne.symm hf.2.2.1])).trans hpairPost.2.1
  have hcμ : μ.vars "decode.count" = qs.length :=
    (hemit.frame_var "decode.count" (by simp [RamUnsignedEncoding.command,RamWordBuffer.append,Com.wvars,
      Ne.symm hf.1])).trans hcν
  have hiμ : μ.vars "decode.i" = i :=
    (hemit.frame_var "decode.i" (by simp [RamUnsignedEncoding.command,RamWordBuffer.append,Com.wvars,
      Ne.symm hf.2.1])).trans hiν
  have htμ : Prefix (RamUnsignedBuffer.encode (qs.take (i+1))) array μ := by
    rw [List.take_succ_eq_append_getElem hi']
    simpa only [RamUnsignedBuffer.encode,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil] using hemitPost.1
  have hposμ : μ.vars cursor = 2*(i+1) := by rw [hlength] at hemitPost; omega
  have hroomμ : 2*qs.length < (μ.arrs array).length := by rwa [RamFrames.run_array_length hemit array]
  have hiNext : i+1 < B := by
    simp only [List.length_append,RamUnsignedBuffer.length_encode] at hlen; omega
  have hinc : Run B (.assign "decode.i" (.add (.var "decode.i") (.lit 1))) μ (μ.setVar "decode.i" (i+1)) 4 :=
    Run.assign (evalB_bin (op := .add) (by rw [evalB_var_iff]; exact ⟨hiμ.symm,hiμ ▸ (by omega : i < B)⟩)
      (evalB_lit (by omega)) hiNext)
  refine ⟨μ.setVar "decode.i" (i+1),(hpair.seq (hemit.seq hinc)).mono
    (by simp only [hden]; omega),?_,?_⟩
  · refine ⟨?_,?_,by simpa only [vars_setVar,String.reduceEq,if_true] using (Nat.succ_le_iff.mpr hi'),?_,?_,?_,?_⟩
    · simpa only [Prefix,arrs_setVar] using hpμ
    · simpa only [vars_setVar,String.reduceEq,if_false] using hcμ
    · simpa only [vars_setVar,String.reduceEq,if_false,if_true] using
        hcurμ.trans (by omega : front.length+2*i+2 = front.length+2*(i+1))
    · simpa only [Prefix,arrs_setVar,vars_setVar,String.reduceEq,if_true] using htμ
    · simpa only [vars_setVar,if_neg hf.2.1,String.reduceEq,if_true] using hposμ
    · simpa only [arrs_setVar] using hroomμ
  · simp [i]

/-- Normalize every input pair into a canonical rational buffer, consuming
exactly the indicated vector and retaining its header and unconsumed tail. -/
theorem command_spec (B K : ℕ) (front tail : List ℕ) (qs : List ℚ≥0) (array cursor : String)
    (h2 : 2 < B) (hlen : (front ++ (RamUnsignedBuffer.encode qs ++ tail)).length+2 < B)
    (hwords : ∀ x ∈ front ++ (RamUnsignedBuffer.encode qs ++ tail), x < B)
    (hsize : ∀ q ∈ qs, q.den.size ≤ K) (harray : array ≠ "input.data")
    (hfresh : cursor ∉ RamDecodeFraction.pair.wvars)
    (hf : cursor ≠ "decode.count" ∧ cursor ≠ "decode.i" ∧ cursor ≠ "decode.cursor" ∧ cursor ≠ "rat.d") :
    Spec B (fun σ => Prefix (front ++ (RamUnsignedBuffer.encode qs ++ tail)) "input.data" σ ∧
      σ.vars "decode.count" = qs.length ∧ σ.vars "decode.cursor" = front.length ∧
      2*qs.length < (σ.arrs array).length) (command array cursor)
      (fun _ τ => Prefix (front ++ (RamUnsignedBuffer.encode qs ++ tail)) "input.data" τ ∧
        τ.vars "decode.cursor" = front.length+2*qs.length ∧ Prefix (RamUnsignedBuffer.encode qs) array τ ∧
        τ.vars cursor = 2*qs.length) ((36*K+56)*qs.length+8) := by
  have hcount : qs.length < B := by
    simp only [List.length_append,RamUnsignedBuffer.length_encode] at hlen; omega
  have hscan := Spec.forRangeZero "decode.i" "decode.count" (Invariant front tail qs array cursor)
    qs.length (36*K+52) hcount (fun _ h => h.2.2.1) (fun _ h => h.2.1)
      (step_spec B K front tail qs array cursor h2 hlen hwords hsize harray hfresh hf)
  rintro σ ⟨hp,hcountσ,hcursorσ,hroom⟩
  let ν := σ.setVar cursor 0
  have hzero : Run B (.assign cursor (.lit 0)) σ ν 2 := Run.assign (evalB_lit (by omega))
  have hinit : Invariant front tail qs array cursor (ν.setVar "decode.i" 0) := by
    refine ⟨?_,?_,by simp,?_,?_,?_,?_⟩
    · simpa only [Prefix,ν,arrs_setVar] using hp
    · simpa only [ν,vars_setVar,String.reduceEq,if_false,if_neg (Ne.symm hf.1)] using hcountσ
    · simpa only [ν,vars_setVar,String.reduceEq,if_false,if_true,if_neg (Ne.symm hf.2.2.1),
        Nat.mul_zero,Nat.add_zero] using hcursorσ
    · intro i hi
      simp only [vars_setVar,if_true,List.take_zero,RamUnsignedBuffer.encode,
        List.flatMap_nil,List.length_nil] at hi
      omega
    · simp only [ν,vars_setVar,if_neg hf.2.1,if_true,Nat.mul_zero]
    · simpa only [ν,arrs_setVar] using hroom
  obtain ⟨τ,hr,hpost⟩ := hscan ν hinit
  refine ⟨τ,(hzero.seq hr).mono (by simp only [Nat.add_assoc,Nat.reduceAdd]; omega),hpost.1.1,?_,?_,?_⟩
  · simpa only [hpost.2] using hpost.1.2.2.2.1
  · simpa only [hpost.2,List.take_length] using hpost.1.2.2.2.2.1
  · simpa only [hpost.2] using hpost.1.2.2.2.2.2.1

end Lax455465Proofs.RamDecodeVector
