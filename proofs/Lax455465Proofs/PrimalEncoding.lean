import Lax455465Proofs.CertificatePostprocessing
import Lax455465Proofs.RamOptimalDecode
import Lax455465Proofs.FlowLpIndices

namespace Lax455465Proofs.PrimalEncoding
open Lax455465.RationalEncoding Lax455465.ProductNetwork DirectedFlowLP
open scoped NNRat

/-- Runtime coordinate order for converting a directed optimum to the
requested edge model; the first (value) coordinate is never halved. -/
def converted {n : ℕ} (kind : EdgeKind) (z : Fin (1+(n*n)*(n*n)) → ℚ)  : List ℚ≥0 :=
  List.ofFn fun i => if kind=.undirected ∧ i.val≠0 then (z i).toNNRat/2 else (z i).toNNRat

theorem ofFn_arcs {n : ℕ} {α : Type} (f : CommodityArc n → α) :
    List.ofFn (fun i => f ((arcIndex n).symm i))=
      (List.ofFn fun s => List.ofFn fun t => List.ofFn fun u => List.ofFn fun v => f ((s,t),(u,v))).flatten.flatten.flatten := by
  rw [List.ofFn_mul]
  simp_rw [List.ofFn_mul]
  simp only [List.flatten_flatten,List.map_ofFn,Function.comp_def]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext s
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext t
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext u
  apply congrArg List.ofFn
  funext v
  have he : (arcIndex n).symm ⟨(s.val*n+t.val)*(n*n)+(u.val*n+v.val),by simpa only [FlowLpIndices.arc_value] using (arcIndex n ((s,t),(u,v))).isLt⟩=((s,t),(u,v)) := by
    apply (arcIndex n).injective
    simp only [Equiv.apply_symm_apply]
    apply Fin.ext
    exact (FlowLpIndices.arc_value s t u v).symm
  exact congrArg f he

def arcValues {n : ℕ} (F : ArcCertificate n) : List ℚ≥0 :=
  List.ofFn fun i => let a := (arcIndex n).symm i; F.arcs a.1.1 a.1.2 a.2.1 a.2.2

theorem converted_eq {n : ℕ} (kind : EdgeKind) (z : Fin (1+(n*n)*(n*n)) → ℚ) :
    converted kind z=[(CertificatePostprocessing.primalFlow z).value]++
      arcValues (CertificatePostprocessing.convertFlow kind (CertificatePostprocessing.primalFlow z)) := by
  unfold converted
  rw [List.ofFn_add]
  apply congrArg₂ List.append
  · simp only [List.ofFn_succ,List.ofFn_zero]
    congr 1
    have hi : (0 : Fin 1).castLE (Nat.le_add_right 1 ((n*n)*(n*n)))=variableIndex n (.inl 0) := by
      apply Fin.ext
      exact (FlowLpIndices.value_variable 0).symm
    rw [hi]
    simp [FlowLpIndices.value_variable,CertificatePostprocessing.primalFlow]
  · apply congrArg List.ofFn
    funext i
    have hi : i.natAdd 1=variableIndex n (.inr ((arcIndex n).symm i)) := by
      apply Fin.ext
      simp [variableIndex,finSumFinEquiv,Equiv.sumCongr]
    have hnz : (i.natAdd 1).val ≠ 0 := by simp
    have hi0 : variableIndex n (.inr ((arcIndex n).symm i)) ≠ 0 := by
      intro h; apply hnz; rw [hi,h]; rfl
    rw [hi]
    cases kind <;> simp [CertificatePostprocessing.convertFlow,CertificatePostprocessing.primalFlow,UndirectedConversion.halve,hi0]

theorem encoded_arcs {n : ℕ} (F : ArcCertificate n) :
    RamUnsignedBuffer.encode ([F.value]++arcValues F)=encodeArcs F := by
  unfold RamUnsignedBuffer.encode arcValues
  rw [ofFn_arcs (fun a : CommodityArc n => F.arcs a.1.1 a.1.2 a.2.1 a.2.2)]
  simp only [List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil]
  unfold encodeArcs
  congr 1
  simp only [List.flatMap_def,List.map_flatten,List.map_ofFn,Function.comp_def]

theorem encoding {n : ℕ} (kind : EdgeKind) (z : Fin (1+(n*n)*(n*n)) → ℚ) :
    RamUnsignedBuffer.encode (converted kind z)=
      encodeArcs (CertificatePostprocessing.convertFlow kind (CertificatePostprocessing.primalFlow z)) := by
  rw [converted_eq]
  have hv : (CertificatePostprocessing.convertFlow kind (CertificatePostprocessing.primalFlow z)).value=
      (CertificatePostprocessing.primalFlow z).value := by cases kind <;> rfl
  rw [←hv]
  exact encoded_arcs _

end Lax455465Proofs.PrimalEncoding
