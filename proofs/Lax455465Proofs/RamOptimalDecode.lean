import Lax455465Proofs.RamCertificateVector
import Lax455465Proofs.RamFlowData
import Lax455465Proofs.FlowOptimalCertificate

namespace Lax455465Proofs.RamOptimalDecode

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamFlowData
open Lax109476.RationalEncoding Lax109476.RationalCertificates
open scoped NNRat

def vector {k : ℕ} (x : Fin k → ℚ) (hx : ∀ i, 0 ≤ x i) : List ℚ≥0 :=
  List.ofFn fun i => (⟨x i,hx i⟩ : ℚ≥0)

@[simp] theorem length_vector {k : ℕ} (x : Fin k → ℚ) (hx : ∀ i, 0 ≤ x i) :
    (vector x hx).length = k := List.length_ofFn

theorem source_vector {k : ℕ} (x : Fin k → ℚ) (hx : ∀ i, 0 ≤ x i) :
    RamCertificateVector.source (vector x hx) = encodeVector x := by
  have hm : (vector x hx).map (fun (q : ℚ≥0) => (q : ℚ)) = List.ofFn x := by
    change (List.ofFn (fun i : Fin k => (⟨x i,hx i⟩ : ℚ≥0))).map
      (fun (q : ℚ≥0) => (q : ℚ)) = List.ofFn x
    erw [List.map_ofFn]
    rfl
  unfold encodeVector
  rw [←hm]
  simp only [RamCertificateVector.source,List.flatMap_map]

/-- Each canonical nonnegative coordinate inherits the word bound of its
signed LP encoding. -/
theorem vector_fits (B : ℕ) {k : ℕ} (x : Fin k → ℚ) (hx : ∀ i, 0 ≤ x i)
    (hwords : ∀ w ∈ encodeVector x, w < B) :
    (∀ q ∈ vector x hx, q.num < B) ∧ (∀ q ∈ vector x hx, q.den < B) := by
  constructor
  · intro q hq
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq
    have hn : (x i).num.natAbs < B := hwords _ (List.mem_flatMap.mpr
      ⟨x i,List.mem_ofFn.mpr ⟨i,rfl⟩,by simp [encodeRational]⟩)
    exact (show NNRat.num (⟨x i,hx i⟩ : ℚ≥0) < B from by
      change (x i).num.natAbs < B
      exact hn)
  · intro q hq
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq
    have hd : (x i).den < B := hwords _ (List.mem_flatMap.mpr
      ⟨x i,List.mem_ofFn.mpr ⟨i,rfl⟩,by simp [encodeRational]⟩)
    exact (show NNRat.den (⟨x i,hx i⟩ : ℚ≥0) < B from by
      change (x i).den < B
      exact hd)

/-- Decode the returned LP witness vectors into canonical unsigned buffers.
All loop limits are the dimensions already computed from the source graph. -/
def command : Com := .seq (.assign "cert.cursor" (.lit 1))
  (.seq (.assign "cert.count" (.var "lp.columns"))
    (.seq (RamCertificateVector.command "flow.primal")
      (.seq (.assign "cert.count" (.var "lp.rows"))
        (RamCertificateVector.command "flow.dual"))))

theorem command_spec (B : ℕ) {n : ℕ} (I : Lax455465.RationalEncoding.RationalInstance n)
    (z : Fin (columns n) → ℚ) (y : Fin (rows n) → ℚ)
    (hz : ∀ i, 0 ≤ z i) (hy : ∀ i, 0 ≤ y i)
    (h3 : 3 < B) (hlen : 1+3*columns n+3*rows n+3 < B)
    (hzn : ∀ q ∈ vector z hz, q.num < B) (hzd : ∀ q ∈ vector z hz, q.den < B)
    (hyn : ∀ q ∈ vector y hy, q.num < B) (hyd : ∀ q ∈ vector y hy, q.den < B) :
    Spec B (fun σ => Data I σ ∧ Prefix (encodeCertificate (.optimal z y)) "vm.output" σ ∧
      2*columns n < (σ.arrs "flow.primal").length ∧ 2*rows n < (σ.arrs "flow.dual").length)
      command (fun _ τ => Data I τ ∧ Prefix (encodeCertificate (.optimal z y)) "vm.output" τ ∧
        Prefix (RamUnsignedBuffer.encode (vector z hz)) "flow.primal" τ ∧
        Prefix (RamUnsignedBuffer.encode (vector y hy)) "flow.dual" τ ∧
        τ.vars "cert.cursor" = 1+3*columns n+3*rows n) (39*(columns n+rows n)+22) := by
  rintro σ ⟨hdata,hp,hproom,hdroom⟩
  let ν := (σ.setVar "cert.cursor" 1).setVar "cert.count" (columns n)
  have hstart1 : Run B (.assign "cert.cursor" (.lit 1)) σ (σ.setVar "cert.cursor" 1) 2 :=
    Run.assign (evalB_lit (by omega))
  have hstart2 : Run B (.assign "cert.count" (.var "lp.columns")) (σ.setVar "cert.cursor" 1) ν 2 :=
    Run.assign (by rw [evalB_var_iff]; simpa only [vars_setVar,String.reduceEq,if_false]
      using And.intro hdata.2.2.2.2.1.symm (hdata.2.2.2.2.1 ▸ (by omega : columns n < B)))
  have hsource : encodeCertificate (.optimal z y) =
      [0] ++ (RamCertificateVector.source (vector z hz) ++ encodeVector y) := by
    simp only [encodeCertificate,source_vector,List.append_assoc]
  obtain ⟨μ,hprimal,hprimalPost⟩ := RamCertificateVector.command_spec B [0] (encodeVector y)
    (vector z hz) "flow.primal" h3 (by simp; omega) hzn hzd (by decide) ν
      ⟨by simpa only [Prefix,ν,arrs_setVar,←hsource] using hp,
       by simp [ν],by simp [ν],by simpa only [length_vector,ν,arrs_setVar] using hproom⟩
  have hdataμ := RamFlowData.frame (hstart1.seq (hstart2.seq hprimal)) I hdata (by decide) (by decide)
  let ρ := μ.setVar "cert.count" (rows n)
  have hcount : Run B (.assign "cert.count" (.var "lp.rows")) μ ρ 2 :=
    Run.assign (by rw [evalB_var_iff]; exact ⟨hdataμ.2.2.2.1.symm,hdataμ.2.2.2.1 ▸ (by omega : rows n < B)⟩)
  let front := [0] ++ encodeVector z
  have hfront : front.length = 1+3*columns n := by
    change ([0] ++ RamVectorEncoding.encode (List.ofFn z)).length = _
    simp only [List.length_append,List.length_cons,List.length_nil,RamVectorEncoding.length_encode,List.length_ofFn]
  have hsource2 : encodeCertificate (.optimal z y) =
      front ++ (RamCertificateVector.source (vector y hy) ++ []) := by
    simp only [front,source_vector,encodeCertificate,List.append_nil]
  have hdroomρ : 2*rows n < (ρ.arrs "flow.dual").length := by
    simp only [ρ,arrs_setVar,RamFrames.run_array_length hprimal "flow.dual",ν,arrs_setVar]
    exact hdroom
  obtain ⟨τ,hdual,hdualPost⟩ := RamCertificateVector.command_spec B front [] (vector y hy) "flow.dual" h3
    (by rw [hfront,length_vector]; omega) hyn hyd (by decide) ρ
      ⟨by simpa only [Prefix,ρ,arrs_setVar,←hsource2,hsource] using hprimalPost.1,
       by simp [ρ],by simpa only [ρ,vars_setVar,String.reduceEq,if_false,List.length_cons,List.length_nil,
         length_vector,hfront] using hprimalPost.2.1,by simpa only [length_vector] using hdroomρ⟩
  have hwhole := hstart1.seq (hstart2.seq (hprimal.seq (hcount.seq hdual)))
  refine ⟨τ,hwhole.mono (by simp only [length_vector]; omega),
    RamFlowData.frame hwhole I hdata (by decide) (by decide),?_,?_,hdualPost.2.2.1,?_⟩
  · simpa only [hsource2] using hdualPost.1
  · simpa only [Prefix,hdual.frame_arr "flow.primal" (by decide),ρ,arrs_setVar] using hprimalPost.2.2.1
  · simpa only [hfront,length_vector] using hdualPost.2.1

end Lax455465Proofs.RamOptimalDecode
