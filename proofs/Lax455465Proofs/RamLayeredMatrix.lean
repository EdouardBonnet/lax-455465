import Lax455465Proofs.RamLayeredData
import Lax455465Proofs.RamFlowMatrix

namespace Lax455465Proofs.RamLayeredMatrix
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamVirtualState
open LayeredFlowLP LayeredLpFlat RamLayeredData
open Lax455465.RationalEncoding

def entry : Com := .seq RamFlowMatrix.decode RamLayeredCoefficient.command

theorem entry_spec (B : ℕ) {n L : ℕ} (I : RationalInstance n)
    (k : Fin (rows n L*columns n L)) (hB : shapeSize n L < B) :
    Spec B (fun σ => Data I L σ ∧ σ.vars "lp.entry"=k.val) entry
      (fun _ τ => Data I L τ ∧ FractionOutput (FlowLpMatrixList.entry (program I L) k) τ) 144 := by
  have hsmall : 2 < B ∧ n < B ∧ n*n < B ∧ L < B ∧ L*(n*n) < B ∧
      (L+1)*n < B ∧ (n*n)*((L+1)*n) < B ∧ rows n L < B ∧ columns n L < B ∧ rows n L*columns n L < B := by
    dsimp only [shapeSize] at hB
    omega
  rcases hsmall with ⟨h2,hn,hn2,hL,hA,hV,hM,hr,hc,hm⟩
  rintro σ ⟨hdata,hk⟩
  obtain ⟨ν,hdecode,hdecoded⟩ := RamFlowMatrix.decode_spec B k.val (columns n L)
    (k.isLt.trans hm) hc σ ⟨hk,hdata.columnCount⟩
  have hdν := frame hdecode I L hdata (by decide) (by decide)
  let ij : Fin (rows n L)×Fin (columns n L) := finProdFinEquiv.symm k
  have hiν : ν.vars "lp.i"=ij.1.val := by
    simpa only [ij,FlowLpMatrixList.rowIndex_value] using hdecoded.1
  have hjν : ν.vars "lp.j"=ij.2.val := by
    simpa only [ij,FlowLpMatrixList.columnIndex_value] using hdecoded.2
  obtain ⟨τ,hcoef,hpost⟩ := RamLayeredCoefficient.command_spec B n L ij.1.val ij.2.val h2 hn hn2 hL hA hV hM
    (ij.1.isLt.trans hr) (by have := ij.2.isLt; omega) ν (context hdν _ _ hiν hjν)
  refine ⟨τ,hdecode.seq hcoef,frame hcoef I L hdν (by decide) (by decide),?_⟩
  rw [coefficient_at I] at hpost
  exact hpost

def command : Com := RamVectorEncoding.command "lp.entry" "lp.matrixLength" entry

/-- Emit all layered matrix coefficients in the exact dense LP encoding order. -/
theorem command_spec (B : ℕ) {n L : ℕ} (I : RationalInstance n) (words : List ℕ)
    (hB : shapeSize n L < B) (hlen : words.length+3*(rows n L*columns n L)+3 < B) :
    Spec B (fun σ => Data I L σ ∧ Prefix words "lp.word" σ ∧ σ.vars "lp.position"=words.length ∧
      words.length+3*(rows n L*columns n L) < (σ.arrs "lp.word").length) command
      (fun _ τ => Data I L τ ∧ Prefix (words++(FlowLpMatrixList.values (program I L)).flatMap
        Lax109476.RationalEncoding.encodeRational) "lp.word" τ ∧
        τ.vars "lp.position"=words.length+3*(rows n L*columns n L))
      (179*(rows n L*columns n L)+6) := by
  have h2 : 2 < B := by dsimp only [shapeSize] at hB; omega
  let qs := FlowLpMatrixList.values (program I L)
  have hlength : qs.length=rows n L*columns n L := by simp [qs,FlowLpMatrixList.values]
  have hheight : ∀ i,∀ hi : i < qs.length,LpInputSize.Height 2 qs[i] := by
    intro i hi
    have hi' : i < rows n L*columns n L := by rwa [hlength] at hi
    simpa only [qs,FlowLpMatrixList.values,List.getElem_ofFn,FlowLpMatrixList.entry,program] using
      LayeredLpSize.coefficient_height
        ((rowIndex n L).symm (finProdFinEquiv.symm (⟨i,hi'⟩ : Fin (rows n L*columns n L))).1)
        ((variableIndex n L).symm (finProdFinEquiv.symm (⟨i,hi'⟩ : Fin (rows n L*columns n L))).2)
  have hh := RamVectorEncoding.command_spec B 144 (Data I L) "lp.entry" "lp.matrixLength" qs words entry
    (by omega) (by simpa only [hlength] using hlen)
    (fun i hi => (hheight i hi).1.trans_lt h2) (fun i hi => (hheight i hi).2.trans_lt h2)
    (fun σ h => by simpa only [hlength] using h.matrixLength)
    (fun σ k h => set_index I L σ "lp.entry" k h (by decide))
    (fun i hi => by
      have hi' : i < rows n L*columns n L := by rwa [hlength] at hi
      simpa only [qs,FlowLpMatrixList.values,List.getElem_ofFn] using entry_spec B I ⟨i,hi'⟩ hB)
    (by decide) (by decide) (by decide) (by decide)
    (fun hr h => frame hr I L h (by decide) (by decide)) (by decide)
  simpa only [command,hlength,qs,RamVectorEncoding.encode,Nat.reduceAdd] using hh

end Lax455465Proofs.RamLayeredMatrix
