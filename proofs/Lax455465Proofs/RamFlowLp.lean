import Lax455465Proofs.RamFlowMatrix
import Lax455465Proofs.RamFlowVectors

namespace Lax455465Proofs.RamFlowLp

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamVirtualState DirectedFlowLP
open RamFlowData Lax109476.RationalEncoding
open scoped NNRat

def header : Com := .seq (.assign "lp.position" (.lit 0))
  (.seq (RamWordBuffer.append "lp.word" "lp.position" (.var "lp.rows"))
    (RamWordBuffer.append "lp.word" "lp.position" (.var "lp.columns")))

theorem header_spec (B : ℕ) {n : ℕ} (I : Lax455465.RationalEncoding.RationalInstance n)
    (h2 : 2 < B) (hr : rows n < B) (hc : columns n < B) :
    Spec B (fun σ => Data I σ ∧ 2 < (σ.arrs "lp.word").length) header
      (fun _ τ => Data I τ ∧ Prefix [rows n,columns n] "lp.word" τ ∧ τ.vars "lp.position" = 2) 16 := by
  rintro σ ⟨hdata,hroom⟩
  let ν := σ.setVar "lp.position" 0
  have hzero : Run B (.assign "lp.position" (.lit 0)) σ ν 2 := Run.assign (evalB_lit (by omega))
  have hdataν := RamFlowData.frame hzero I hdata (by decide) (by decide)
  obtain ⟨μ,hrow,hrowPost⟩ := RamWordBuffer.append_spec B "lp.word" "lp.position" [] (rows n)
    (.var "lp.rows") (by omega) (by simp; omega) ν
      ⟨by intro i hi; simp at hi,by simp [ν],by simp [ν]; omega,
        by rw [evalB_var_iff]; exact ⟨hdataν.2.2.2.1.symm,hdataν.2.2.2.1 ▸ hr⟩⟩
  have hdataμ := RamFlowData.frame hrow I hdataν (by decide) (by decide)
  have hroomμ : 2 < (μ.arrs "lp.word").length := by
    rw [RamFrames.run_array_length hrow "lp.word"]; simpa only [ν,arrs_setVar] using hroom
  obtain ⟨τ,hcol,hcolPost⟩ := RamWordBuffer.append_spec B "lp.word" "lp.position" [rows n] (columns n)
    (.var "lp.columns") (by omega) (by simp; omega) μ
      ⟨hrowPost.1,by simpa using hrowPost.2,by simp; omega,
        by rw [evalB_var_iff]; exact ⟨hdataμ.2.2.2.2.1.symm,hdataμ.2.2.2.2.1 ▸ hc⟩⟩
  exact ⟨τ,hzero.seq (hrow.seq hcol),RamFlowData.frame hcol I hdataμ (by decide) (by decide),
    by simpa using hcolPost.1,by simpa using hcolPost.2⟩

abbrev wordLength (n : ℕ) := 2+3*(rows n*columns n+rows n+columns n)

def cost (n M : ℕ) : ℕ :=
  (36*(M*M).size+239)*(rows n*columns n)+53*rows n+45*columns n+34

/-- Construct the entire dense flow LP using only initialized graph data
and runtime dimensions. The header and all matrix/vector loops are fixed. -/
def command : Com := .seq header (.seq RamFlowMatrix.command
  (.seq RamFlowVectors.bounds RamFlowVectors.objectives))

/-- The actual constructed buffer equals the exact public LP input word,
including every dimension, matrix coefficient, row bound, and objective. -/
theorem command_spec (B M : ℕ) {n : ℕ} (I : Lax455465.RationalEncoding.RationalInstance n)
    (hM : 1 ≤ M) (hB : 2*M^2+3 < B)
    (hni : 2*n+1 < B) (hn2 : n*n < B) (hn3 : (n*n)*n < B)
    (hr : rows n < B) (hc : columns n < B) (hm : rows n*columns n < B)
    (hcindex : 2*(n*n)+1 < B) (hlen : wordLength n+3 < B)
    (hnum : ∀ z, (I.weight z).num ≤ M) (hden : ∀ z, (I.weight z).den ≤ M)
    (hcapnum : ∀ u v, (I.capacity u v).num ≤ M) (hcapden : ∀ u v, (I.capacity u v).den ≤ M) :
    Spec B (fun σ => Data I σ ∧ wordLength n < (σ.arrs "lp.word").length) command
      (fun _ τ => Data I τ ∧ Prefix (encodeProgram (program I)) "lp.word" τ ∧
        τ.vars "lp.position" = (encodeProgram (program I)).length) (cost n M) := by
  have h2 : 2 < B := by nlinarith
  have hMB : M < B := by nlinarith
  rintro σ ⟨hdata,hroom⟩
  obtain ⟨ν,hhead,hheadPost⟩ := header_spec B I h2 hr hc σ ⟨hdata,by dsimp only [wordLength] at hroom; omega⟩
  obtain ⟨μ,hmat,hmatPost⟩ := RamFlowMatrix.command_spec B M I [rows n,columns n] hM hB hni hn2 hn3 hr hc hm
    (by simp only [List.length_cons,List.length_nil,wordLength] at *; omega) hnum hden ν
      ⟨hheadPost.1,hheadPost.2.1,by simpa using hheadPost.2.2,
        by rw [RamFrames.run_array_length hhead "lp.word"]; simp only [List.length_cons,List.length_nil];
           dsimp only [wordLength] at hroom; omega⟩
  let matrixWords := [rows n,columns n] ++ (FlowLpMatrixList.values (program I)).flatMap encodeRational
  have hmatrixLength : matrixWords.length = 2+3*(rows n*columns n) := by
    change ([rows n,columns n] ++ RamVectorEncoding.encode (FlowLpMatrixList.values (program I))).length = _
    simp only [List.length_append,List.length_cons,List.length_nil,RamVectorEncoding.length_encode,
      FlowLpMatrixList.values,List.length_ofFn]
  have hroomμ : wordLength n < (μ.arrs "lp.word").length := by
    rw [RamFrames.run_array_length hmat "lp.word",RamFrames.run_array_length hhead "lp.word"]; exact hroom
  obtain ⟨ρ,hbounds,hboundsPost⟩ := RamFlowVectors.bounds_spec B M I matrixWords (by omega) hn2 hr hcindex hM hMB
    (by rw [hmatrixLength]; dsimp only [wordLength] at hlen; omega) hcapnum hcapden μ
      ⟨hmatPost.1,hmatPost.2.1,by simpa only [List.length_cons,List.length_nil,hmatrixLength] using hmatPost.2.2,
        by rw [hmatrixLength]; dsimp only [wordLength] at hroomμ; omega⟩
  let boundWords := matrixWords ++ encodeVector (program I).b
  have hboundLength : boundWords.length = 2+3*(rows n*columns n)+3*rows n := by
    change (matrixWords ++ RamVectorEncoding.encode (List.ofFn (program I).b)).length = _
    simp only [List.length_append,RamVectorEncoding.length_encode,List.length_ofFn,hmatrixLength]
  have hroomρ : wordLength n < (ρ.arrs "lp.word").length := by
    rw [RamFrames.run_array_length hbounds "lp.word"]; exact hroomμ
  obtain ⟨τ,hobj,hobjPost⟩ := RamFlowVectors.objectives_spec B I boundWords (by omega) hc
    (by rw [hboundLength]; dsimp only [wordLength] at hlen; omega) ρ
      ⟨hboundsPost.1,hboundsPost.2.1,by rw [hboundLength]; simpa only [hmatrixLength] using hboundsPost.2.2,
        by rw [hboundLength]; dsimp only [wordLength] at hroomρ; omega⟩
  have hencoded : boundWords ++ encodeVector (program I).c = encodeProgram (program I) := by
    simp only [boundWords,matrixWords,FlowLpMatrixList.values_eq,encodeProgram]
  have hencodedLength : (encodeProgram (program I)).length = 2+3*(rows n*columns n)+3*rows n+3*columns n := by
    rw [←hencoded]
    change (boundWords ++ RamVectorEncoding.encode (List.ofFn (program I).c)).length = _
    simp only [List.length_append,RamVectorEncoding.length_encode,List.length_ofFn,hboundLength]
  refine ⟨τ,(hhead.seq (hmat.seq (hbounds.seq hobj))).mono (by simp only [cost]; omega),hobjPost.1,?_,?_⟩
  · simpa only [hencoded] using hobjPost.2.1
  · simpa only [hencodedLength,hboundLength] using hobjPost.2.2

end Lax455465Proofs.RamFlowLp
