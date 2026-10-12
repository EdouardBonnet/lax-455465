import Lax455465Proofs.RamFlowConvert
import Lax455465Proofs.RamEmitWords
import Lax455465Proofs.CutScoreData

namespace Lax455465Proofs.RamJointOutput
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamRegionContext
open Lax455465.RationalEncoding Lax455465.ProductNetwork
open scoped NNRat

def emit : Com := .seq (.assign "emit.count" (.var "metric.n"))
  (.seq (RamEmitWords.command "cut.flags" 2)
    (.seq (.assign "emit.count" (.mul (.lit 2) (.var "lp.columns")))
      (RamEmitWords.command "flow.converted" 1)))
def command : Com := .seq RamFlowConvert.command emit

def cost (n k M : ℕ) : ℕ := RamFlowConvert.cost k M+13*n+26*k+18

theorem mask_data {n : ℕ} (S : Finset (Fin n)) {σ : Env}
    (hp : Prefix (RamUnsignedBuffer.encode (CutScoreData.vertexFlags S)) "cut.flags" σ) :
    RamEmitWords.Data "cut.flags" 2 (encodeCut S) σ := by
  intro i hi
  have hi' : i < n := by simpa only [encodeCut,List.length_ofFn] using hi
  have hflags : (CutScoreData.vertexFlags S).length=n := List.length_ofFn
  have hidx : 2*i < (RamUnsignedBuffer.encode (CutScoreData.vertexFlags S)).length := by
    rw [RamUnsignedBuffer.length_encode,hflags]; omega
  have hn := RamUnsignedBuffer.numerator_at (CutScoreData.vertexFlags S) i (by omega)
  rw [List.getElem?_eq_getElem hidx] at hn
  have h := (hp (2*i) hidx).trans hn
  simpa [encodeCut,CutScoreData.vertexFlags,MaskedMassData.flags,ResidualData.mask,apply_ite] using h

theorem buffer_data (xs : List ℕ) {σ : Env} (hp : Prefix xs "flow.converted" σ) :
    RamEmitWords.Data "flow.converted" 1 xs σ := by
  intro i hi
  simpa only [Nat.one_mul] using hp i hi

theorem emit_spec (B : ℕ) {n : ℕ} (S : Finset (Fin n)) (qs : List ℚ≥0) (front : List ℕ)
    (h2 : 2 < B) (hvertex : 2*n < B) (hlen : 2*qs.length < B)
    (hq : ∀ q∈qs,q.num < B ∧ q.den < B) :
    Spec B (fun σ => σ.vars "metric.n"=n ∧ σ.vars "lp.columns"=qs.length ∧
      Prefix (RamUnsignedBuffer.encode (CutScoreData.vertexFlags S)) "cut.flags" σ ∧
      Prefix (RamUnsignedBuffer.encode qs) "flow.converted" σ ∧ σ.out=front) emit
      (fun _ τ => τ.out=front++encodeCut S++RamUnsignedBuffer.encode qs) (13*n+26*qs.length+18) := by
  rintro σ ⟨hn,hcols,hmask,hflow,hout⟩
  let ν := σ.setVar "emit.count" n
  have r1 : Run B (.assign "emit.count" (.var "metric.n")) σ ν 2 := Run.assign (by
    rw [evalB_var_iff]; exact ⟨hn.symm,hn ▸ (by omega : n < B)⟩)
  have hcutlen : (encodeCut S).length=n := List.length_ofFn
  have hcutwords : ∀ x∈encodeCut S,x < B := by
    intro x hx
    obtain ⟨v,rfl⟩ := List.mem_ofFn.mp hx
    split_ifs <;> omega
  obtain ⟨μ,r2,p2⟩ := RamEmitWords.command_spec B "cut.flags" 2 (encodeCut S) front (by omega) h2
    (by rwa [hcutlen]) (by rw [hcutlen]; omega) hcutwords ν
    ⟨mask_data S hmask,by simp [ν,hcutlen],hout⟩
  let ρ := μ.setVar "emit.count" (2*qs.length)
  have hcμ : μ.vars "lp.columns"=qs.length :=
    (r2.frame_var "lp.columns" (by decide)).trans (by simpa [ν] using hcols)
  have r3 : Run B (.assign "emit.count" (.mul (.lit 2) (.var "lp.columns"))) μ ρ 4 := Run.assign
    (evalB_bin (op := .mul) (evalB_lit h2)
      (by rw [evalB_var_iff]; exact ⟨hcμ.symm,hcμ ▸ (by omega : qs.length < B)⟩) hlen)
  have hflowρ : Prefix (RamUnsignedBuffer.encode qs) "flow.converted" ρ := by
    simpa only [Prefix,ρ,arrs_setVar,r2.frame_arr "flow.converted" (by decide),ν,arrs_setVar] using hflow
  have hwords : ∀ x∈RamUnsignedBuffer.encode qs,x < B := by
    intro x hx
    obtain ⟨q,hq',hx⟩ := List.mem_flatMap.mp hx
    simp only [encodeRational,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl
    · exact (hq q hq').1
    · exact (hq q hq').2
  obtain ⟨τ,r4,p4⟩ := RamEmitWords.command_spec B "flow.converted" 1 (RamUnsignedBuffer.encode qs)
    (front++encodeCut S) (by omega) (by omega)
    (by simpa only [Nat.one_mul,RamUnsignedBuffer.length_encode] using hlen)
    (by simpa only [RamUnsignedBuffer.length_encode] using hlen) hwords ρ
    ⟨buffer_data _ hflowρ,by simp [ρ],p2⟩
  exact ⟨τ,(r1.seq (r2.seq (r3.seq r4))).mono (by rw [hcutlen,RamUnsignedBuffer.length_encode]; omega),p4⟩

/-- The fixed output command writes the selected cut followed by the
converted primal flow, with exact canonical rational encoding. -/
theorem command_spec (B M : ℕ) {n : ℕ} (kind : EdgeKind) (S : Finset (Fin n))
    (qs : List ℚ≥0) (front : List ℕ) (h2 : 2 < B) (hB : 2*M < B)
    (hvertex : 2*n < B) (hlen : 2*qs.length+2 < B)
    (hq : ∀ q∈qs,LpInputSize.Height M (q : ℚ)) :
    Spec B (fun σ => RamFlowConvert.Context kind qs σ ∧ σ.vars "metric.n"=n ∧
      Prefix (RamUnsignedBuffer.encode (CutScoreData.vertexFlags S)) "cut.flags" σ ∧
      2*qs.length < (σ.arrs "flow.converted").length ∧ σ.out=front) command
      (fun _ τ => τ.out=front++encodeCut S++RamUnsignedBuffer.encode (RamFlowConvert.values kind qs))
      (cost n qs.length M) := by
  rintro σ ⟨hc,hn,hmask,hroom,hout⟩
  obtain ⟨ν,r1,p1⟩ := RamFlowConvert.command_spec B M kind qs h2 hB hlen hq σ ⟨hc,hroom⟩
  have hvlen : (RamFlowConvert.values kind qs).length=qs.length := List.length_ofFn
  have hwords : ∀ q∈RamFlowConvert.values kind qs,q.num < B ∧ q.den < B := by
    intro q hmem
    obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hmem
    have hh := RamFlowConvert.value_height M kind qs hq i hi
    exact ⟨(num_bound hh).trans_lt hB,(den_bound hh).trans_lt hB⟩
  obtain ⟨τ,r2,p2⟩ := emit_spec B S (RamFlowConvert.values kind qs) front h2 hvertex
    (by rw [hvlen]; omega) hwords ν
    ⟨(r1.frame_var "metric.n" (by decide)).trans hn,p1.1.2.1.trans hvlen.symm,
      by simpa only [Prefix,r1.frame_arr "cut.flags" (by decide)] using hmask,p1.2,
      (r1.out_eq (by decide)).trans hout⟩
  exact ⟨τ,(r1.seq r2).mono (by rw [hvlen]; dsimp [cost]; omega),p2⟩

/-- Specialization to the exact LP coordinate layout gives the public
joint certificate, with no information supplied on the output tape. -/
theorem primal_spec (B M : ℕ) {n : ℕ} (kind : EdgeKind) (S : Finset (Fin n))
    (z : Fin (1+(n*n)*(n*n)) → ℚ) (hz : ∀ i,0 ≤ z i)
    (h2 : 2 < B) (hB : 2*M < B) (hvertex : 2*n < B)
    (hlen : 2*(1+(n*n)*(n*n))+2 < B) (hq : ∀ i,LpInputSize.Height M (z i)) :
    Spec B (fun σ => RamFlowConvert.Context kind (RamOptimalDecode.vector z hz) σ ∧ σ.vars "metric.n"=n ∧
      Prefix (RamUnsignedBuffer.encode (CutScoreData.vertexFlags S)) "cut.flags" σ ∧
      2*(1+(n*n)*(n*n)) < (σ.arrs "flow.converted").length ∧ σ.out=[]) command
      (fun _ τ => τ.out=Lax455465.FlowCutCertificate.encodeCertificate
        ⟨S,CertificatePostprocessing.convertFlow kind (CertificatePostprocessing.primalFlow z)⟩)
      (cost n (1+(n*n)*(n*n)) M) := by
  have hh : ∀ q∈RamOptimalDecode.vector z hz,LpInputSize.Height M (q : ℚ) := by
    intro q hmem
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hmem
    exact hq i
  rintro σ hσ
  obtain ⟨τ,rr,pr⟩ := command_spec B M kind S (RamOptimalDecode.vector z hz) [] h2 hB hvertex
    (by simpa only [RamOptimalDecode.length_vector] using hlen) hh σ (by simpa only [RamOptimalDecode.length_vector] using hσ)
  refine ⟨τ,by simpa only [RamOptimalDecode.length_vector] using rr,?_⟩
  simpa only [List.nil_append,RamFlowConvert.primal_values,PrimalEncoding.encoding,
    Lax455465.FlowCutCertificate.encodeCertificate] using pr

end Lax455465Proofs.RamJointOutput
