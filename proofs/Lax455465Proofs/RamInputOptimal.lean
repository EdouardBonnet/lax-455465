import Lax455465Proofs.RamInputFlowLp
import Lax455465Proofs.RamOptimalDecode

namespace Lax455465Proofs.RamInputOptimal

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamFlowData DirectedFlowLP
open Lax455465.RationalEncoding Lax455465.ProductNetwork
open Lax109476.LinearProgram Lax109476.RationalCertificates
open Lax759944.BinaryWordEncoding Lax759944.RamPolytime
open scoped NNRat

/-- A single native command obtains and decodes the actual optimal pair.
Its only initialized mathematical input is the physical graph tape. -/
theorem exists_program :
    ∃ (c : Com) (timeBound wordBound sourceTime sourceWord : Polynomial ℕ),
      ∀ {n : ℕ} (kind : EdgeKind) (I : RationalInstance n), 2 ≤ supportCount I.weights →
        ∃ (z : Fin (columns n) → ℚ) (y : Fin (rows n) → ℚ)
          (hz : PrimalFeasible (program I) z) (hy : DualFeasible (program I) y),
          primalValue (program I) z = dualValue (program I) y ∧
          FitsInWords (sourceWord.eval (bitSize (Lax109476.RationalEncoding.encodeProgram (program I))))
            (Lax109476.RationalEncoding.encodeCertificate (.optimal z y)) ∧
          ∀ W : ℕ, wordBound.eval (bitSize (encodeInput kind I)) ≤ W →
            Spec (2^W) (fun σ => σ.inp = (encodeInput kind I).length :: encodeInput kind I ∧
              (encodeInput kind I).length ≤ (σ.arrs "input.data").length ∧
              2*n < (σ.arrs "flow.weights").length ∧ 2*(n*n) < (σ.arrs "flow.capacities").length ∧
              RamFlowLp.wordLength n < (σ.arrs "lp.word").length ∧
              (Lax109476.RationalEncoding.encodeProgram (program I)).length < (σ.arrs "vm.input").length ∧
              sourceTime.eval (bitSize (Lax109476.RationalEncoding.encodeProgram (program I))) < (σ.arrs "vm.addresses").length ∧
              sourceTime.eval (bitSize (Lax109476.RationalEncoding.encodeProgram (program I))) < (σ.arrs "vm.values").length ∧
              sourceTime.eval (bitSize (Lax109476.RationalEncoding.encodeProgram (program I))) < (σ.arrs "vm.output").length ∧
              2*columns n < (σ.arrs "flow.primal").length ∧ 2*rows n < (σ.arrs "flow.dual").length)
              c (fun _ τ => Data I τ ∧ τ.vars "flow.kind" = RamGraphHeader.tag kind ∧
                Prefix (RamUnsignedBuffer.encode (RamOptimalDecode.vector z hz.1)) "flow.primal" τ ∧
                Prefix (RamUnsignedBuffer.encode (RamOptimalDecode.vector y hy.1)) "flow.dual" τ ∧
                Prefix (Lax109476.RationalEncoding.encodeCertificate (.optimal z y)) "vm.output" τ ∧
                τ.vars "cert.cursor" = 1+3*columns n+3*rows n)
              (timeBound.eval (bitSize (encodeInput kind I))) := by
  obtain ⟨c,T,WB,TB,sourceWord,hsolver⟩ := RamInputFlowLp.exists_program
  let extra : Polynomial ℕ := Polynomial.C 39*LpInputSize.sizeBound+Polynomial.C 22
  let words : Polynomial ℕ := WB+LpInputSize.sizeBound+Polynomial.C 10
  refine ⟨.seq c RamOptimalDecode.command,T+extra,words,TB,sourceWord,?_⟩
  intro n kind I hp
  obtain ⟨certificate,hvalid,hfit,hcorrect⟩ := hsolver kind I
  obtain ⟨z,y,hcertificate,hz,hy,hvalue⟩ := FlowOptimalCertificate.optimal I hp certificate hvalid
  subst certificate
  refine ⟨z,y,hz,hy,hvalue,hfit,?_⟩
  intro W hW
  let L := bitSize (encodeInput kind I)
  let S := LpInputSize.sizeBound.eval L
  have hsum : WB.eval L+S+10 ≤ W := by simpa [words,L,S] using hW
  have hWB : WB.eval L ≤ W := by omega
  have hB : W < 2^W := Nat.lt_two_pow_self
  have hLPword : RamFlowLp.wordLength n ≤ S := by
    rw [←FlowEncodingSizes.flow_length I]
    exact (WordSize.length_le _).trans (LpInputSize.flow_program_polynomial_size kind I)
  have h3 : 3 < 2^W := by omega
  have hlen : 1+3*columns n+3*rows n+3 < 2^W := by
    dsimp only [RamFlowLp.wordLength] at hLPword
    omega
  rintro σ ⟨hinp,hinputRoom,hwroom,hcroom,hlproom,hvinput,hA,hV,hO,hpr,hdu⟩
  obtain ⟨ν,hrun,hpost⟩ := hcorrect W hWB σ
    ⟨hinp,hinputRoom,hwroom,hcroom,hlproom,hvinput,hA,hV,hO⟩
  have hzwords : ∀ x ∈ Lax109476.RationalEncoding.encodeVector z, x < 2^W := by
    intro x hx
    exact hpost.2.2.1 x (by
      simp only [Lax109476.RationalEncoding.encodeCertificate,List.mem_append]
      exact Or.inl (Or.inr hx))
  have hywords : ∀ x ∈ Lax109476.RationalEncoding.encodeVector y, x < 2^W := by
    intro x hx
    exact hpost.2.2.1 x (by
      simp only [Lax109476.RationalEncoding.encodeCertificate,List.mem_append]
      exact Or.inr hx)
  obtain ⟨hzn,hzd⟩ := RamOptimalDecode.vector_fits (2^W) z hz.1 hzwords
  obtain ⟨hyn,hyd⟩ := RamOptimalDecode.vector_fits (2^W) y hy.1 hywords
  obtain ⟨τ,hdecode,hdecoded⟩ := RamOptimalDecode.command_spec (2^W) I z y hz.1 hy.1 h3 hlen hzn hzd hyn hyd ν
    ⟨hpost.1,hpost.2.2.2.1,by rwa [RamFrames.run_array_length hrun "flow.primal"],
      by rwa [RamFrames.run_array_length hrun "flow.dual"]⟩
  have hcost : 39*(columns n+rows n)+22 ≤ extra.eval L := by
    simp only [extra,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C]
    dsimp only [RamFlowLp.wordLength] at hLPword
    dsimp only [S] at hLPword
    omega
  refine ⟨τ,(hrun.seq hdecode).mono ?_,hdecoded.1,
    (hdecode.frame_var "flow.kind" (by decide)).trans hpost.2.1,
    hdecoded.2.2.1,hdecoded.2.2.2.1,hdecoded.2.1,hdecoded.2.2.2.2⟩
  simp only [Polynomial.eval_add]
  dsimp only [L] at hcost
  omega

end Lax455465Proofs.RamInputOptimal
