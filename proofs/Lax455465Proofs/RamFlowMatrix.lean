import Lax455465Proofs.RamFlowData
import Lax455465Proofs.RamFlowCoefficient
import Lax455465Proofs.RamVectorEncoding
import Lax455465Proofs.FlowLpMatrixList
import Lax455465Proofs.LpInputSize

namespace Lax455465Proofs.RamFlowMatrix

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamVirtualState DirectedFlowLP
open RamFlowData
open scoped NNRat

def decode : Com := .seq (.assign "lp.i" (.div (.var "lp.entry") (.var "lp.columns")))
  (.assign "lp.j" (.sub (.var "lp.entry") (.mul (.var "lp.i") (.var "lp.columns"))))

theorem decode_spec (B k c : ℕ) (hk : k < B) (hc : c < B) :
    Spec B (fun σ => σ.vars "lp.entry" = k ∧ σ.vars "lp.columns" = c) decode
      (fun _ τ => τ.vars "lp.i" = k/c ∧ τ.vars "lp.j" = k%c) 10 := by
  have hdiv : k/c < B := (Nat.div_le_self _ _).trans_lt hk
  have hprod : k/c*c < B := (Nat.div_mul_le_self _ _).trans_lt hk
  have hmod : k%c < B := (Nat.mod_le _ _).trans_lt hk
  rintro σ ⟨he,hcσ⟩
  run_vcg
  all_goals simp_all [Nat.mod_def,Nat.mul_comm]

def entry : Com := .seq decode RamFlowCoefficient.command

theorem entry_spec (B M : ℕ) {n : ℕ} (I : Lax455465.RationalEncoding.RationalInstance n)
    (k : Fin (rows n*columns n)) (hB : 2*M^2+3 < B)
    (hni : 2*n+1 < B) (hn2 : n*n < B) (hn3 : (n*n)*n < B)
    (hr : rows n < B) (hc : columns n < B) (hm : rows n*columns n < B)
    (hnum : ∀ z, (I.weight z).num ≤ M) (hden : ∀ z, (I.weight z).den ≤ M) :
    Spec B (fun σ => Data I σ ∧ σ.vars "lp.entry" = k.val) entry
      (fun _ τ => Data I τ ∧ FractionOutput (FlowLpMatrixList.entry (program I) k) τ)
      (36*(M*M).size+204) := by
  rintro σ ⟨hdata,hk⟩
  obtain ⟨ν,hdecode,hdecoded⟩ := decode_spec B k.val (columns n) (k.isLt.trans hm) hc σ
    ⟨hk,hdata.2.2.2.2.1⟩
  have hdataν := RamFlowData.frame hdecode I hdata (by decide) (by decide)
  let ij : Fin (rows n) × Fin (columns n) := finProdFinEquiv.symm k
  let r : Row n := (rowIndex n).symm ij.1
  let v : Variable n := (variableIndex n).symm ij.2
  have hiν : ν.vars "lp.i" = (rowIndex n r).val := by
    simpa only [r,Equiv.apply_symm_apply,ij,FlowLpMatrixList.rowIndex_value] using hdecoded.1
  have hjν : ν.vars "lp.j" = (variableIndex n v).val := by
    simpa only [v,Equiv.apply_symm_apply,ij,FlowLpMatrixList.columnIndex_value] using hdecoded.2
  have hctx : RamFlowContext.Context n (rowIndex n r).val (variableIndex n v).val (List.ofFn I.weight) ν :=
    ⟨hdataν.1,hdataν.2.1,hdataν.2.2.1,hiν,hjν,hdataν.2.2.2.2.2.2.1⟩
  obtain ⟨τ,hcoefficient,hpost⟩ := RamFlowCoefficient.command_spec B M I r v hB hni hn2 hn3
    (by simpa only [r,Equiv.apply_symm_apply] using ij.1.isLt.trans hr)
    (by simpa only [v,Equiv.apply_symm_apply] using ij.2.isLt.trans hc) hnum hden ν hctx
  have hdataτ := RamFlowData.frame hcoefficient I hdataν (by decide) (by decide)
  refine ⟨τ,(hdecode.seq hcoefficient).mono (by omega),hdataτ,?_⟩
  simpa only [FlowLpMatrixList.entry,program,r,v,ij] using hpost

/-- A single numerical loop emits all matrix entries in exact row order. -/
def command : Com := RamVectorEncoding.command "lp.entry" "lp.matrixLength" entry

theorem command_spec (B M : ℕ) {n : ℕ} (I : Lax455465.RationalEncoding.RationalInstance n)
    (words : List ℕ) (hM : 1 ≤ M) (hB : 2*M^2+3 < B)
    (hni : 2*n+1 < B) (hn2 : n*n < B) (hn3 : (n*n)*n < B)
    (hr : rows n < B) (hc : columns n < B) (hm : rows n*columns n < B)
    (hlen : words.length+3*(rows n*columns n)+3 < B)
    (hnum : ∀ z, (I.weight z).num ≤ M) (hden : ∀ z, (I.weight z).den ≤ M) :
    Spec B (fun σ => Data I σ ∧ Prefix words "lp.word" σ ∧ σ.vars "lp.position" = words.length ∧
      words.length+3*(rows n*columns n) < (σ.arrs "lp.word").length) command
      (fun _ τ => Data I τ ∧ Prefix (words ++ (FlowLpMatrixList.values (program I)).flatMap
        Lax109476.RationalEncoding.encodeRational) "lp.word" τ ∧
        τ.vars "lp.position" = words.length+3*(rows n*columns n))
      ((36*(M*M).size+239)*(rows n*columns n)+6) := by
  have h1 : 1 < B := by nlinarith
  let qs := FlowLpMatrixList.values (program I)
  have hlength : qs.length = rows n*columns n := by simp [qs,FlowLpMatrixList.values]
  have hheight : ∀ i, ∀ hi : i < qs.length, LpInputSize.Height (M*M) qs[i] := by
    intro i hi
    have hix : i < rows n*columns n := by rwa [hlength] at hi
    have hw : ∀ z, LpInputSize.Height M (I.weight z : ℚ) := fun z => by
      simpa only [LpInputSize.Height,NNRat.natAbs_num_coe,NNRat.den_coe] using And.intro (hnum z) (hden z)
    simpa only [qs,FlowLpMatrixList.values,List.getElem_ofFn,FlowLpMatrixList.entry,program]
      using LpInputSize.coefficient_height I M hM hw
        ((rowIndex n).symm (finProdFinEquiv.symm (⟨i,hix⟩ : Fin (rows n*columns n))).1)
        ((variableIndex n).symm (finProdFinEquiv.symm (⟨i,hix⟩ : Fin (rows n*columns n))).2)
  have hMM : M*M < B := by nlinarith
  have hloop := RamVectorEncoding.command_spec B (36*(M*M).size+204) (Data I)
    "lp.entry" "lp.matrixLength" qs words entry h1 (by simpa only [hlength] using hlen)
    (fun i hi => (hheight i hi).1.trans_lt hMM) (fun i hi => (hheight i hi).2.trans_lt hMM)
    (fun σ h => by simpa only [hlength] using h.2.2.2.2.2.1)
    (fun σ k h => RamFlowData.set_index I σ "lp.entry" k h (by decide))
    (fun i hi => by
      have hix : i < rows n*columns n := by rwa [hlength] at hi
      simpa only [qs,FlowLpMatrixList.values,List.getElem_ofFn] using
        entry_spec B M I ⟨i,hix⟩ hB hni hn2 hn3 hr hc hm hnum hden)
    (by decide) (by decide) (by decide) (by decide)
    (fun hrun h => RamFlowData.frame hrun I h (by decide) (by decide)) (by decide)
  simpa only [command,hlength,qs,RamVectorEncoding.encode,Nat.add_assoc,Nat.reduceAdd] using hloop

end Lax455465Proofs.RamFlowMatrix
