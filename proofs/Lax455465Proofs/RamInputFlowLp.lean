import Lax455465Proofs.RamUniformFlowLp
import Lax455465Proofs.RamGraphInput
import Lax455465Proofs.RamInputCopy

namespace Lax455465Proofs.RamInputFlowLp

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamFlowData DirectedFlowLP
open Lax455465.RationalEncoding Lax455465.ProductNetwork Lax109476.RationalCertificates
open Lax759944.BinaryWordEncoding Lax759944.RamPolytime
open scoped NNRat

theorem input_length {n : ℕ} (kind : EdgeKind) (I : RationalInstance n) :
    (encodeInput kind I).length = 2+2*n+2*(n*n) := by
  rw [FlowInputLists.input_eq]
  simp only [List.length_append,List.length_cons,List.length_nil,RamUnsignedBuffer.length_encode,
    List.length_ofFn,capacities]
  omega

/-- One fixed native command reads the physical graph input, constructs the
exact flow LP, and obtains a valid certificate from the registered solver.
No graph dimensions, coefficients, or certificate coordinates are preloaded. -/
theorem exists_program :
    ∃ (c : Com) (timeBound wordBound sourceTime sourceWord : Polynomial ℕ),
      c.NoWrite ∧ ∀ {n : ℕ} (kind : EdgeKind) (I : RationalInstance n),
        ∃ certificate : Certificate (rows n) (columns n),
          IsValidCertificate (program I) certificate ∧
          FitsInWords (sourceWord.eval (bitSize (Lax109476.RationalEncoding.encodeProgram (program I))))
            (Lax109476.RationalEncoding.encodeCertificate certificate) ∧
          ∀ W : ℕ, wordBound.eval (bitSize (encodeInput kind I)) ≤ W →
            Spec (2^W) (fun σ => σ.inp = (encodeInput kind I).length :: encodeInput kind I ∧
              (encodeInput kind I).length ≤ (σ.arrs "input.data").length ∧
              2*n < (σ.arrs "flow.weights").length ∧ 2*(n*n) < (σ.arrs "flow.capacities").length ∧
              RamFlowLp.wordLength n < (σ.arrs "lp.word").length ∧
              (Lax109476.RationalEncoding.encodeProgram (program I)).length < (σ.arrs "vm.input").length ∧
              sourceTime.eval (bitSize (Lax109476.RationalEncoding.encodeProgram (program I))) < (σ.arrs "vm.addresses").length ∧
              sourceTime.eval (bitSize (Lax109476.RationalEncoding.encodeProgram (program I))) < (σ.arrs "vm.values").length ∧
              sourceTime.eval (bitSize (Lax109476.RationalEncoding.encodeProgram (program I))) < (σ.arrs "vm.output").length)
              c (fun _ τ => Data I τ ∧ τ.vars "flow.kind" = RamGraphHeader.tag kind ∧
                (∀ x ∈ Lax109476.RationalEncoding.encodeCertificate certificate, x < 2^W) ∧
                Prefix (Lax109476.RationalEncoding.encodeCertificate certificate) "vm.output" τ ∧
                τ.vars "vm.outputLength" = (Lax109476.RationalEncoding.encodeCertificate certificate).length ∧
                τ.vars "vm.running" = 0) (timeBound.eval (bitSize (encodeInput kind I))) := by
  obtain ⟨c,T,WB,TB,sourceWord,hnoWrite,hsolver⟩ := RamUniformFlowLp.exists_program
  let parsing : Polynomial ℕ := Polynomial.C 200*(Polynomial.X+Polynomial.C 1)^2
  let words : Polynomial ℕ := WB+LpInputSize.sizeBound+Polynomial.X+Polynomial.C 10
  refine ⟨.seq RamInputCopy.copy (.seq RamGraphInput.command c),T+parsing,words,TB,sourceWord,⟨by decide,by decide,hnoWrite⟩,?_⟩
  intro n kind I
  obtain ⟨certificate,hvalid,hfit,hcorrect⟩ := hsolver kind I
  refine ⟨certificate,hvalid,hfit,?_⟩
  intro W hW
  let L := bitSize (encodeInput kind I)
  let S := LpInputSize.sizeBound.eval L
  have hsum : WB.eval L+S+L+10 ≤ W := by simpa [words,L,S] using hW
  have hWB : WB.eval L ≤ W := by omega
  have hB : W < 2^W := Nat.lt_two_pow_self
  have hlenL : (encodeInput kind I).length ≤ L := WordSize.length_le _
  have hLPword : RamFlowLp.wordLength n ≤ S := by
    rw [←FlowEncodingSizes.flow_length I]
    exact (WordSize.length_le _).trans (LpInputSize.flow_program_polynomial_size kind I)
  have hr : rows n < 2^W := by dsimp only [RamFlowLp.wordLength] at hLPword; omega
  have hc : columns n < 2^W := by dsimp only [RamFlowLp.wordLength] at hLPword; omega
  have hm : rows n*columns n < 2^W := by dsimp only [RamFlowLp.wordLength] at hLPword; omega
  have hn2 : n*n < 2^W := by dsimp only [rows] at hr; omega
  have hn3 : (n*n)*n < 2^W := by dsimp only [rows] at hr; omega
  have hn : n < 2^W := by rw [input_length] at hlenL; omega
  have h3 : 3 < 2^W := by omega
  have hwords : ∀ x ∈ encodeInput kind I, x < 2^W := by
    intro x hx
    exact lt_of_lt_of_le (WordSize.member_bound _ x hx)
      (Nat.pow_le_pow_right (by decide) (by omega : L ≤ W))
  have hwsize : ∀ u, (I.weight u).den.size ≤ L := by
    intro u
    have := WordSize.member_size _ _ (LpInputSize.weight_members kind I u (I.weight u).den (by simp [encodeRational]))
    omega
  have hcsize : ∀ u v, (I.capacity u v).den.size ≤ L := by
    intro u v
    have := WordSize.member_size _ _ (LpInputSize.capacity_members kind I u v (I.capacity u v).den (by simp [encodeRational]))
    omega
  rintro σ ⟨hinp,hinputRoom,hwroom,hcroom,hlproom,hvinput,hA,hV,hO⟩
  obtain ⟨ν,hcopy,hcopyPost⟩ := RamInputCopy.copy_spec (2^W) (encodeInput kind I) (by omega)
    (by omega) hwords σ ⟨hinp,hinputRoom⟩
  have hwroomν : 2*n < (ν.arrs "flow.weights").length := by rwa [RamFrames.run_array_length hcopy "flow.weights"]
  have hcroomν : 2*(n*n) < (ν.arrs "flow.capacities").length := by rwa [RamFrames.run_array_length hcopy "flow.capacities"]
  obtain ⟨μ,hgraph,hgraphPost⟩ := RamGraphInput.command_spec (2^W) L kind I (by omega) hn hn2 hn3 hr hc hm
    (by omega) hwords hwsize hcsize ν ⟨hcopyPost.2.2,hwroomν,hcroomν⟩
  have hprefixRun := hcopy.seq hgraph
  obtain ⟨τ,hsolve,hpost⟩ := hcorrect W hWB μ ⟨hgraphPost.1,
    by rwa [RamFrames.run_array_length hprefixRun "lp.word"],
    by rwa [RamFrames.run_array_length hprefixRun "vm.input"],
    by rwa [RamFrames.run_array_length hprefixRun "vm.addresses"],
    by rwa [RamFrames.run_array_length hprefixRun "vm.values"],
    by rwa [RamFrames.run_array_length hprefixRun "vm.output"]⟩
  have hcount : n+n*n ≤ L := by rw [input_length] at hlenL; omega
  have hparseCost : 12*(encodeInput kind I).length+7+((36*L+56)*(n+n*n)+52) ≤ parsing.eval L := by
    have hprod := Nat.mul_le_mul_left (36*L+56) hcount
    simp only [parsing,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,
      Polynomial.eval_add,Polynomial.eval_X]
    nlinarith [sq_nonneg (L : ℤ)]
  refine ⟨τ,(hcopy.seq (hgraph.seq hsolve)).mono ?_,hpost.1,
    hpost.2.1.trans hgraphPost.2,hpost.2.2⟩
  simp only [Polynomial.eval_add]
  dsimp only [L] at hparseCost ⊢
  omega

end Lax455465Proofs.RamInputFlowLp
