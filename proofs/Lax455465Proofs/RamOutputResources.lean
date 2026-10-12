import Lax455465Proofs.RamJointOutput
import Lax455465Proofs.RamRoundingResources

namespace Lax455465Proofs.RamOutputResources
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465.RationalEncoding Lax455465.ProductNetwork Lax759944.BinaryWordEncoding
open scoped NNRat

noncomputable def timeBound (P : Polynomial ℕ) : Polynomial ℕ :=
  (36*(P+2)+90)*(1+Polynomial.X^4)+13*Polynomial.X+26
noncomputable def wordBound (P : Polynomial ℕ) : Polynomial ℕ :=
  2*P+2*(1+Polynomial.X^4)+2*Polynomial.X+16

theorem time_bound (P : Polynomial ℕ) {n : ℕ} (kind : EdgeKind) (I : RationalInstance n) :
    RamJointOutput.cost n (1+(n*n)*(n*n)) (2^(P.eval (bitSize (encodeInput kind I)))) ≤
      (timeBound P).eval (bitSize (encodeInput kind I)) := by
  let L := bitSize (encodeInput kind I)
  let w := P.eval L
  have hn : n ≤ L := LpInputSize.input_dimension kind I
  have hs : (2*2^w).size=w+2 := by
    rw [show 2*2^w=2^(w+1) by rw [pow_succ,Nat.mul_comm],Nat.size_pow]
  simp only [RamJointOutput.cost,RamFlowConvert.cost,RamFlowConvert.bodyCost,timeBound,
    Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_one,Polynomial.eval_X,Polynomial.eval_pow]
  change (36*(2*2^w).size+42+22)*(1+n*n*(n*n))+8+13*n+26*(1+n*n*(n*n))+18 ≤
    (36*(w+2)+90)*(1+L^4)+13*L+26
  have hcols : 1+n*n*(n*n) ≤ 1+L^4 := by
    simpa only [pow_succ,pow_zero,Nat.mul_one,Nat.one_mul,Nat.mul_assoc] using
      Nat.add_le_add_left (Nat.pow_le_pow_left hn 4) 1
  rw [hs]
  have hm := Nat.mul_le_mul_left (36*(w+2)+90) hcols
  nlinarith

theorem host_bounds (P : Polynomial ℕ) {n : ℕ} (kind : EdgeKind) (I : RationalInstance n) (W : ℕ)
    (hW : (wordBound P).eval (bitSize (encodeInput kind I)) ≤ W) :
    2 < 2^W ∧ 2*2^(P.eval (bitSize (encodeInput kind I))) < 2^W ∧
      2*n < 2^W ∧ 2*(1+(n*n)*(n*n))+2 < 2^W := by
  let L := bitSize (encodeInput kind I)
  let w := P.eval L
  have hn : n ≤ L := LpInputSize.input_dimension kind I
  have hcols : 1+n*n*(n*n) ≤ 1+L^4 := by
    simpa only [pow_succ,pow_zero,Nat.mul_one,Nat.one_mul,Nat.mul_assoc] using
      Nat.add_le_add_left (Nat.pow_le_pow_left hn 4) 1
  have hW' : 2*w+2*(1+L^4)+2*L+16 ≤ W := by simpa [wordBound,L,w] using hW
  have hWP : W < 2^W := Nat.lt_two_pow_self
  have hp : 2^(w+2) ≤ 2^W := Nat.pow_le_pow_right (by decide) (by omega)
  have hpos := Nat.two_pow_pos w
  have htwice : 2*2^w < 2^W := by rw [pow_add] at hp; norm_num at hp; omega
  exact ⟨by omega,htwice,by omega,by omega⟩

/-- The complete certificate writer, including fraction reduction for the
undirected model, has polynomial resources in the source input size. -/
theorem command_spec (P : Polynomial ℕ) {n : ℕ} (kind : EdgeKind) (I : RationalInstance n) (S : Finset (Fin n))
    (z : Fin (1+(n*n)*(n*n)) → ℚ) (hz : ∀ i,0 ≤ z i)
    (hheight : ∀ i,LpInputSize.Height (2^(P.eval (bitSize (encodeInput kind I)))) (z i))
    (W : ℕ) (hW : (wordBound P).eval (bitSize (encodeInput kind I)) ≤ W) :
    Spec (2^W) (fun σ => RamFlowConvert.Context kind (RamOptimalDecode.vector z hz) σ ∧ σ.vars "metric.n"=n ∧
      RamVirtualState.Prefix (RamUnsignedBuffer.encode (CutScoreData.vertexFlags S)) "cut.flags" σ ∧
      2*(1+(n*n)*(n*n)) < (σ.arrs "flow.converted").length ∧ σ.out=[]) RamJointOutput.command
      (fun _ τ => τ.out=Lax455465.FlowCutCertificate.encodeCertificate
        ⟨S,CertificatePostprocessing.convertFlow kind (CertificatePostprocessing.primalFlow z)⟩)
      ((timeBound P).eval (bitSize (encodeInput kind I))) := by
  obtain ⟨h2,hB,hvertex,hlen⟩ := host_bounds P kind I W hW
  intro σ hσ
  obtain ⟨τ,rr,pr⟩ := RamJointOutput.primal_spec (2^W) (2^(P.eval (bitSize (encodeInput kind I))))
    kind S z hz h2 hB hvertex hlen hheight σ hσ
  exact ⟨τ,rr.mono (time_bound P kind I),pr⟩

end Lax455465Proofs.RamOutputResources
