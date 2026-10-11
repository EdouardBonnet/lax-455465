import Lax455465Proofs.VolumeData
import Lax455465Proofs.RamArrayScalar
import Lax455465Proofs.RamRootDistances
import Lax455465Proofs.RamDualDistancesInit

namespace Lax455465Proofs.RamVolumeCoefficient

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamVirtualState RamUnsignedScalar MetricMatrix DirectedFlowLP
open scoped NNRat

def Context {n : ℕ} (outward : Bool) (capacity length : Matrix n) (distance : Fin n → ℚ≥0)
    (radius : ℚ≥0) (σ : Env) : Prop :=
  σ.vars "metric.n" = n ∧ σ.vars "metric.n2" = n*n ∧ Stored "portion.radius" radius σ ∧
    Prefix (RamUnsignedBuffer.encode (values capacity)) "region.capacities" σ ∧
    Prefix (RamUnsignedBuffer.encode (values length)) "metric.old" σ ∧
    Prefix (RamUnsignedBuffer.encode (List.ofFn distance)) (RamRootDistances.array outward) σ

theorem frame {B K : ℕ} {cmd : Com} {σ τ : Env} (hr : Run B cmd σ τ K)
    {n : ℕ} {outward : Bool} {capacity length : Matrix n} {distance : Fin n → ℚ≥0}
    {radius : ℚ≥0} (h : Context outward capacity length distance radius σ)
    (hx : ∀ x ∈ ["metric.n","metric.n2","portion.radius.n","portion.radius.d"], x ∉ cmd.wvars)
    (ha : ∀ a ∈ ["region.capacities","metric.old",RamRootDistances.array outward], a ∉ cmd.warrs) :
    Context outward capacity length distance radius τ := by
  simpa only [Context,Stored,Prefix,String.reduceAppend,
    hr.frame_var "metric.n" (hx _ (by simp)),hr.frame_var "metric.n2" (hx _ (by simp)),
    hr.frame_var "portion.radius.n" (hx _ (by simp)),hr.frame_var "portion.radius.d" (hx _ (by simp)),
    hr.frame_arr "region.capacities" (ha _ (by simp)),hr.frame_arr "metric.old" (ha _ (by simp)),
    hr.frame_arr (RamRootDistances.array outward) (ha _ (by simp))] using h

def baseIndex (outward : Bool) : String := if outward then "metric.u" else "metric.v"

def command (outward : Bool) : Com := .seq (.assign "metric.entry" (.var "sum.i"))
  (.seq RamDualDistancesInit.indices
    (.seq (RamArrayScalar.command "metric.old" "sum.i" "portion.length")
      (.seq (RamArrayScalar.command (RamRootDistances.array outward) (baseIndex outward) "portion.base")
        (.seq RamEdgePortion.command
          (.seq (RamUnsignedArithmetic.copy "left")
            (.seq (RamUnsignedBuffer.read "region.capacities" "sum.i")
              (.seq (RamUnsignedArithmetic.copy "right") multiplyFraction)))))))

set_option maxHeartbeats 1600000 in
/-- Compute one exact clipped contribution, reading the edge length, base
distance, radius, and residual capacity from their actual runtime buffers. -/
theorem command_spec (B M : ℕ) {n : ℕ} (outward : Bool) (capacity length : Matrix n)
    (distance : Fin n → ℚ≥0) (radius : ℚ≥0) (u v : Fin n)
    (hB : 2*M^2+3 < B) (hn : n < B) (hn2 : n*n < B)
    (hindex : 2*(n*n)+2 < B) (hvertex : 2*n+2 < B)
    (hcn : (capacity u v).num ≤ M) (hcd : (capacity u v).den ≤ M)
    (hln : (length u v).num ≤ M) (hld : (length u v).den ≤ M)
    (hdn : (VolumeData.base outward distance u v).num ≤ M) (hdd : (VolumeData.base outward distance u v).den ≤ M)
    (hrn : radius.num ≤ M) (hrd : radius.den ≤ M)
    (htn : (RamTruncatedSubtract.value radius (VolumeData.base outward distance u v)).num ≤ M)
    (htd : (RamTruncatedSubtract.value radius (VolumeData.base outward distance u v)).den ≤ M)
    (hpn : (RamEdgePortion.value (length u v) (VolumeData.base outward distance u v) radius).num ≤ M)
    (hpd : (RamEdgePortion.value (length u v) (VolumeData.base outward distance u v) radius).den ≤ M) :
    Spec B (fun σ => Context outward capacity length distance radius σ ∧ σ.vars "sum.i"=(edgeIndex n (u,v)).val)
      (command outward) (fun _ τ => Context outward capacity length distance radius τ ∧
        FractionOutput ((capacity u v * RamEdgePortion.value (length u v) (VolumeData.base outward distance u v) radius : ℚ≥0) : ℚ) τ)
      (72*(M^2).size+382) := by
  have hM : M < B := by nlinarith
  have h2 : 2 < B := by nlinarith
  let idx := (edgeIndex n (u,v)).val
  let base := VolumeData.base outward distance u v
  let portion := RamEdgePortion.value (length u v) base radius
  let t := if outward then u else v
  have hbase : (List.ofFn distance)[t.val] = base := by
    simp only [List.getElem_ofFn,base,t,VolumeData.base]
    cases outward <;> rfl
  have hi : idx < n*n := (edgeIndex n (u,v)).isLt
  rintro σ ⟨hctx,hentry⟩
  let σ₁ := σ.setVar "metric.entry" idx
  have r₁ : Run B (.assign "metric.entry" (.var "sum.i")) σ σ₁ 2 :=
    Run.assign (by rw [evalB_var_iff]; exact ⟨hentry.symm,hentry ▸ hi.trans hn2⟩)
  have hctx₁ := frame r₁ hctx (by decide) (by simp [Com.warrs])
  obtain ⟨σ₂,r₂,p₂⟩ := RamDualDistancesInit.indices_spec B u v hn hn2 σ₁ ⟨hctx₁.1,by simp [σ₁,idx]⟩
  have hctx₂ := frame r₂ hctx₁ (by decide) (by simp [RamDualDistancesInit.indices,Com.warrs])
  have hi₂ : σ₂.vars "sum.i"=idx := (r₂.frame_var _ (by decide)).trans ((r₁.frame_var _ (by decide)).trans hentry)
  obtain ⟨σ₃,r₃,p₃⟩ := RamArrayScalar.command_spec B "metric.old" "sum.i" "portion.length" (values length) idx
    (by simpa only [length_values] using hi) h2 (by omega)
    (by rw [value_at]; exact hln.trans_lt hM) (by rw [value_at]; exact hld.trans_lt hM)
    (by decide) (by decide) σ₂ ⟨hctx₂.2.2.2.2.1,hi₂⟩
  have hctx₃ := frame r₃ hctx₂ (by decide) (by simp [RamArrayScalar.command,RamUnsignedBuffer.read,save,Com.warrs])
  have ht₃ : σ₃.vars (baseIndex outward) = t.val := by
    have hx : σ₂.vars (baseIndex outward) = t.val := by
      cases outward with
      | false => exact p₂.2
      | true => exact p₂.1
    exact (r₃.frame_var _ (by cases outward <;> decide)).trans hx
  obtain ⟨σ₄,r₄,p₄⟩ := RamArrayScalar.command_spec B (RamRootDistances.array outward) (baseIndex outward) "portion.base"
    (List.ofFn distance) t.val (by simpa only [List.length_ofFn] using t.isLt) h2 (by omega)
    (by rw [hbase]; exact hdn.trans_lt hM) (by rw [hbase]; exact hdd.trans_lt hM)
    (by cases outward <;> decide) (by decide) σ₃ ⟨hctx₃.2.2.2.2.2,ht₃⟩
  have hctx₄ := frame r₄ hctx₃
    (by cases outward <;> decide)
    (by cases outward <;> simp [RamArrayScalar.command,RamUnsignedBuffer.read,save,Com.warrs])
  have hlength : Stored "portion.length" (length u v) σ₄ := by
    simpa only [idx,value_at,Stored,String.reduceAppend,r₄.frame_var "portion.length.n" (by cases outward <;> decide),
      r₄.frame_var "portion.length.d" (by cases outward <;> decide)] using p₃
  obtain ⟨σ₅,r₅,p₅⟩ := RamEdgePortion.command_spec B M (length u v) base radius hB hln hld hdn hdd hrn hrd htn htd σ₄
    ⟨hlength,by simpa only [hbase] using p₄,hctx₄.2.2.1⟩
  have hctx₅ := frame r₅ hctx₄ (by decide) (by intro a ha; change a ∉ ([] : List String); simp)
  obtain ⟨σ₆,r₆,p₆⟩ := RamUnsignedArithmetic.copy_spec B portion "left" (by omega) (hpn.trans_lt hM) (hpd.trans_lt hM) (by decide) σ₅ p₅
  have hctx₆ := frame r₆ hctx₅ (by decide) (by simp [RamUnsignedArithmetic.copy,Com.warrs])
  have hi₆ : σ₆.vars "sum.i"=idx := by
    have rr := r₁.seq (r₂.seq (r₃.seq (r₄.seq (r₅.seq r₆))))
    exact (rr.frame_var _ (by cases outward <;> decide)).trans hentry
  obtain ⟨σ₇,r₇,p₇⟩ := RamUnsignedBuffer.read_spec B "region.capacities" "sum.i" (values capacity) idx
    (by simpa only [length_values] using hi) h2 (by omega)
    (by rw [value_at]; exact hcn.trans_lt hM) (by rw [value_at]; exact hcd.trans_lt hM) (by decide) σ₆ ⟨hctx₆.2.2.2.1,hi₆⟩
  obtain ⟨σ₈,r₈,p₈⟩ := RamUnsignedArithmetic.copy_spec B (capacity u v) "right" (by omega)
    (hcn.trans_lt hM) (hcd.trans_lt hM) (by decide) σ₇ (by simpa only [idx,value_at] using p₇.1)
  have hleft : σ₈.vars "left.s"=0 ∧ σ₈.vars "left.n"=portion.num ∧ σ₈.vars "left.d"=portion.den := by
    have rr := r₇.seq r₈
    simpa only [rr.frame_var "left.s" (by decide),rr.frame_var "left.n" (by decide),rr.frame_var "left.d" (by decide),String.reduceAppend] using p₆
  obtain ⟨τ,r₉,p₉⟩ := multiplyFraction_spec B M 0 portion.num portion.den 0 (capacity u v).num (capacity u v).den
    hB (by omega) (by omega) hpn hpd hcn hcd portion.den_pos (capacity u v).den_pos σ₈
    ⟨hleft.1,hleft.2.1,hleft.2.2,by simpa only [String.reduceAppend] using p₈⟩
  have rr := r₁.seq (r₂.seq (r₃.seq (r₄.seq (r₅.seq (r₆.seq (r₇.seq (r₈.seq r₉)))))))
  refine ⟨τ,rr.mono ?_,frame rr hctx (by cases outward <;> decide) (by cases outward <;> decide),?_⟩
  · have ha : (radius.den*base.den).size ≤ (M^2).size := Nat.size_le_size (by nlinarith [Nat.mul_le_mul hrd hdd])
    have hb : (portion.den*(capacity u v).den).size ≤ (M^2).size := Nat.size_le_size (by nlinarith [Nat.mul_le_mul hpd hcd])
    omega
  · simpa only [RamUnsignedArithmetic.value,portion,base,NNRat.coe_mul,mul_comm] using p₉

end Lax455465Proofs.RamVolumeCoefficient
