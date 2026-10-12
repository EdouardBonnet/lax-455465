import Lax455465Proofs.RamLayeredMatrix
import Lax455465Proofs.RamLayeredVectors

namespace Lax455465Proofs.RamLayeredLp
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState
open LayeredFlowLP LayeredLpFlat RamLayeredData Lax109476.RationalEncoding
open scoped NNRat

def header : Com := RamFlowLp.header

theorem header_spec (B : ℕ) {n L : ℕ} (I : Lax455465.RationalEncoding.RationalInstance n)
    (h2 : 2 < B) (hr : rows n L < B) (hc : columns n L < B) :
    Spec B (fun σ => Data I L σ ∧ 2 < (σ.arrs "lp.word").length) header
      (fun _ τ => Data I L τ ∧ Prefix [rows n L,columns n L] "lp.word" τ ∧ τ.vars "lp.position"=2) 16 := by
  rintro σ ⟨hdata,hroom⟩
  let ν := σ.setVar "lp.position" 0
  have hzero : Run B (.assign "lp.position" (.lit 0)) σ ν 2 := Run.assign (evalB_lit (by omega))
  have hdν := frame hzero I L hdata (by decide) (by decide)
  obtain ⟨μ,hrow,hp⟩ := RamWordBuffer.append_spec B "lp.word" "lp.position" [] (rows n L)
    (.var "lp.rows") (by omega) (by simp; omega) ν
      ⟨by intro i hi; simp at hi,by simp [ν],by simp [ν]; omega,
        by rw [evalB_var_iff]; exact ⟨hdν.rowCount.symm,hdν.rowCount ▸ hr⟩⟩
  have hdμ := frame hrow I L hdν (by decide) (by decide)
  have hroomμ : 2 < (μ.arrs "lp.word").length := by
    rw [RamFrames.run_array_length hrow "lp.word"]
    exact hroom
  obtain ⟨τ,hcol,hp'⟩ := RamWordBuffer.append_spec B "lp.word" "lp.position" [rows n L] (columns n L)
    (.var "lp.columns") (by omega) (by simp; omega) μ
      ⟨hp.1,by simpa using hp.2,by simp; omega,
        by rw [evalB_var_iff]; exact ⟨hdμ.columnCount.symm,hdμ.columnCount ▸ hc⟩⟩
  exact ⟨τ,hzero.seq (hrow.seq hcol),frame hcol I L hdμ (by decide) (by decide),
    by simpa using hp'.1,by simpa using hp'.2⟩

def cost (n L : ℕ) : ℕ := 179*(rows n L*columns n L)+53*rows n L+45*columns n L+34

/-- Construct the entire layered LP from graph capacities and a runtime
layer budget. Matrix entries, bounds, and objective use the public LP encoding. -/
def command : Com := .seq header (.seq RamLayeredMatrix.command
  (.seq RamLayeredVectors.bounds RamLayeredVectors.objectives))

theorem command_spec (B M : ℕ) {n L : ℕ} (I : Lax455465.RationalEncoding.RationalInstance n)
    (hM : 1 ≤ M) (hMB : M < B) (hB : shapeSize n L < B)
    (hcindex : 2*(n*n)+1 < B) (hlen : LayeredLpSize.wordLength n L+3 < B)
    (hnum : ∀ u v,(I.capacity u v).num ≤ M) (hden : ∀ u v,(I.capacity u v).den ≤ M) :
    Spec B (fun σ => Data I L σ ∧ LayeredLpSize.wordLength n L < (σ.arrs "lp.word").length) command
      (fun _ τ => Data I L τ ∧ Prefix (encodeProgram (program I L)) "lp.word" τ ∧
        τ.vars "lp.position"=(encodeProgram (program I L)).length) (cost n L) := by
  have hsmall : 2 < B ∧ n*n < B ∧ rows n L < B ∧ columns n L < B := by
    dsimp only [shapeSize] at hB
    omega
  rcases hsmall with ⟨h2,hn2,hr,hc⟩
  rintro σ ⟨hdata,hroom⟩
  obtain ⟨ν,hhead,hheadPost⟩ := header_spec B I h2 hr hc σ
    ⟨hdata,by dsimp only [LayeredLpSize.wordLength] at hroom; omega⟩
  obtain ⟨μ,hmat,hmatPost⟩ := RamLayeredMatrix.command_spec B I [rows n L,columns n L] hB
    (by simp only [List.length_cons,List.length_nil,LayeredLpSize.wordLength] at *; omega) ν
    ⟨hheadPost.1,hheadPost.2.1,by simpa using hheadPost.2.2,
      by rw [RamFrames.run_array_length hhead "lp.word"]
         simp only [List.length_cons,List.length_nil]
         dsimp only [LayeredLpSize.wordLength] at hroom
         omega⟩
  let matrixWords := [rows n L,columns n L]++(FlowLpMatrixList.values (program I L)).flatMap encodeRational
  have hmatrixLength : matrixWords.length=2+3*(rows n L*columns n L) := by
    change ([rows n L,columns n L]++RamVectorEncoding.encode (FlowLpMatrixList.values (program I L))).length=_
    simp only [List.length_append,List.length_cons,List.length_nil,RamVectorEncoding.length_encode,
      FlowLpMatrixList.values,List.length_ofFn]
  have hroomμ : LayeredLpSize.wordLength n L < (μ.arrs "lp.word").length := by
    rw [RamFrames.run_array_length hmat "lp.word",RamFrames.run_array_length hhead "lp.word"]
    exact hroom
  obtain ⟨ρ,hbounds,hboundsPost⟩ := RamLayeredVectors.bounds_spec B M I matrixWords (by omega) hn2 hr hcindex hM hMB
    (by rw [hmatrixLength]; dsimp only [LayeredLpSize.wordLength] at hlen; omega) hnum hden μ
    ⟨hmatPost.1,hmatPost.2.1,by simpa only [List.length_cons,List.length_nil,hmatrixLength] using hmatPost.2.2,
      by rw [hmatrixLength]; dsimp only [LayeredLpSize.wordLength] at hroomμ; omega⟩
  let boundWords := matrixWords++encodeVector (program I L).b
  have hboundLength : boundWords.length=2+3*(rows n L*columns n L)+3*rows n L := by
    change (matrixWords++RamVectorEncoding.encode (List.ofFn (program I L).b)).length=_
    simp only [List.length_append,RamVectorEncoding.length_encode,List.length_ofFn,hmatrixLength]
  have hroomρ : LayeredLpSize.wordLength n L < (ρ.arrs "lp.word").length := by
    rw [RamFrames.run_array_length hbounds "lp.word"]
    exact hroomμ
  obtain ⟨τ,hobj,hobjPost⟩ := RamLayeredVectors.objectives_spec B I boundWords (by omega) hc
    (by rw [hboundLength]; dsimp only [LayeredLpSize.wordLength] at hlen; omega) ρ
    ⟨hboundsPost.1,hboundsPost.2.1,by rw [hboundLength]; simpa only [hmatrixLength] using hboundsPost.2.2,
      by rw [hboundLength]; dsimp only [LayeredLpSize.wordLength] at hroomρ; omega⟩
  have he : boundWords++encodeVector (program I L).c=encodeProgram (program I L) := by
    simp only [boundWords,matrixWords,FlowLpMatrixList.values_eq,encodeProgram]
  have hencodedLength : (encodeProgram (program I L)).length=
      2+3*(rows n L*columns n L)+3*rows n L+3*columns n L := by
    rw [LayeredLpSize.program_length]
    ring
  refine ⟨τ,(hhead.seq (hmat.seq (hbounds.seq hobj))).mono (by simp only [cost]; omega),hobjPost.1,?_,?_⟩
  · simpa only [he] using hobjPost.2.1
  · simpa only [hencodedLength,hboundLength] using hobjPost.2.2

end Lax455465Proofs.RamLayeredLp
