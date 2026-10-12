import Lax455465Proofs.RamPathEdgeRead
import Lax455465Proofs.RamBottleneckFold

namespace Lax455465Proofs.RamBottleneck
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamRational
open LayeredFlowLP RamPathState RamPathEdgeRead
open scoped NNRat

def edges {n L : ℕ} (qs : Fin (1+(n*n)*(L*(n*n))) → ℚ≥0) (st : Edge n)
    (path : Fin (L+1) → Fin n) : List ℚ≥0 :=
  List.ofFn fun k : Fin L => qs (variableIndex n L (.inr (st,(k,(path k.castSucc,path k.succ)))))

def command : Com := .seq (RamBottleneckFold.command "short.level" "short.layer" RamPathEdgeRead.command)
  (RamUnsignedScalar.save "short.amount")

/-- Compute the actual bottleneck of the stored path, capped by the
remaining demand, using exact native comparisons of residual coordinates. -/
theorem command_spec (B M : ℕ) {n L : ℕ} (qs : Fin (1+(n*n)*(L*(n*n))) → ℚ≥0)
    (st : Edge n) (path : Fin (L+1) → Fin n) (a : ℚ≥0)
    (hB : 2*M^2+3<B)
    (hsize : n+n*n+L*(n*n)+2*(1+(n*n)*(L*(n*n)))+2*L+20<B)
    (hnum : ∀ j,(qs j).num≤M) (hden : ∀ j,(qs j).den≤M) (ha : a.num≤M ∧ a.den≤M) :
    Spec B (fun σ => Context qs st path σ ∧ RamUnsignedScalar.Stored "short.remaining" a σ) command
      (fun _ τ => Context qs st path τ ∧
        RamUnsignedScalar.Stored "short.amount" (Bottleneck.minimum a (edges qs st path)) τ) (122*L+20) := by
  have hMB : M<B := by nlinarith only [hB]
  have hqnum : ∀ q∈edges qs st path,q.num≤M := by
    intro q hq
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hq
    exact hnum _
  have hqden : ∀ q∈edges qs st path,q.den≤M := by
    intro q hq
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hq
    exact hden _
  have hbody : ∀ i,∀ hi : i<(edges qs st path).length,
      Spec B (fun σ => Context qs st path σ ∧ σ.vars "short.level"=i) RamPathEdgeRead.command
        (fun _ τ => Context qs st path τ ∧ FractionOutput ((edges qs st path)[i] : ℚ) τ) 48 := by
    intro i hi
    have hin : i<L := by simpa [edges] using hi
    simpa only [edges,List.getElem_ofFn] using RamPathEdgeRead.command_spec B qs st path ⟨i,hin⟩ hsize
      (fun j => (hnum j).trans_lt hMB) (fun j => (hden j).trans_lt hMB)
  have hr := RamBottleneckFold.command_spec B M 48 (Context qs st path) "short.level" "short.layer"
    a (edges qs st path) RamPathEdgeRead.command hB (by simp only [edges,List.length_ofFn]; omega)
    hqnum hqden ha
    (fun _ h => by simpa only [edges,List.length_ofFn] using h.1.layer)
    (by
      intro σ v name h hn
      rcases hn with rfl | rfl | rfl
      all_goals exact ⟨RamPathState.set_var h.1 _ v (by decide),h.2⟩)
    hbody (by decide) (by decide) (by decide)
    (fun rr h => ⟨data_frame rr h.1 (by decide) (by decide),
      by simpa only [Prefix,rr.frame_arr "short.raw" (by decide)] using h.2⟩)
    (fun rr h => ⟨data_frame rr h.1 (by decide) (by decide),
      by simpa only [Prefix,rr.frame_arr "short.raw" (by decide)] using h.2⟩)
  rintro σ hσ
  obtain ⟨ν,rf,pf⟩ := hr σ hσ
  have hheight := Bottleneck.height M a (edges qs st path) ha (fun q hq => ⟨hqnum q hq,hqden q hq⟩)
  obtain ⟨τ,rs,ps⟩ := RamUnsignedScalar.save_spec B "short.amount" (Bottleneck.minimum a (edges qs st path))
    (hheight.1.trans_lt hMB) (hheight.2.trans_lt hMB) (by decide) ν pf.2
  exact ⟨τ,(rf.seq rs).mono (by simp only [edges,List.length_ofFn]; omega),
    ⟨data_frame rs pf.1.1 (by decide) (by decide),
      by simpa only [Prefix,rs.frame_arr "short.raw" (by decide)] using pf.1.2⟩,ps⟩

end Lax455465Proofs.RamBottleneck
